/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Common

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem shiftLeft_eq_zero_iff (m k : Nat) : m <<< k = 0 ↔ m = 0 := by
  rw [Nat.shiftLeft_eq]; simp

theorem roundedResultOf_ite_zero (sp : Specialization) (dst : Format) (rm : RoundingDirection)
    {x : ℝ} {zn zs : Bool} {S q : Int} (hx : x = (S : ℝ) * 2 ^ q) (hz : S = 0 → zs = zn) :
    RoundedResultOf sp dst rm x zn
      (if S = 0 then (dst.pack zs 0 0, {}) else dst.roundPack sp rm (S < 0) S.natAbs q) := by
  by_cases hS : S = 0
  · subst hS
    simp only [↓reduceIte]
    rw [hz rfl, hx, Int.cast_zero, zero_mul]
    exact roundedResultOf_zero sp dst rm zn
  · simp only [hS, ↓reduceIte]
    rw [hx, intCast_eq_signed_natAbs S]
    exact roundPack_spec sp dst rm _ _ q (Int.natAbs_pos.mpr hS) _

theorem zeroSumSign_eq (rm : RoundingDirection) (sa sb : Bool) (ma mb : Nat) (ka kb : Nat)
    (hS : (if sa then -1 else 1) * ((ma <<< ka : Nat) : Int)
      + (if sb then -1 else 1) * ((mb <<< kb : Nat) : Int) = 0) :
    (if (ma = 0 && mb = 0 && sa == sb) = true then sa
      else decide (rm = RoundingDirection.roundTowardNegative))
      = arithZeroSumNegative rm sa sb := by
  unfold arithZeroSumNegative
  by_cases hs : sa = sb
  · subst hs
    have hma : ma <<< ka = 0 ∧ mb <<< kb = 0 := by
      generalize ma <<< ka = x at hS
      generalize mb <<< kb = y at hS
      cases sa <;> simp only [Bool.false_eq_true, ↓reduceIte] at hS <;> omega
    rw [shiftLeft_eq_zero_iff, shiftLeft_eq_zero_iff] at hma
    obtain ⟨hma, hmb⟩ := hma
    simp [hma, hmb]
  · simp [hs]

theorem roundedResultOf_finite_addition (sp : Specialization) (fa fb dst : Format)
    (rm : RoundingDirection) {a b : Nat} (hfa : IsFinite fa a) (hfb : IsFinite fb b) :
    RoundedResultOf sp dst rm (valR fa a + valR fb b)
      (arithZeroSumNegative rm (fa.unpack a).sign (fb.unpack b).sign)
      (let ua := fa.unpack a
       let ub := fb.unpack b
       let ma := fa.sigOf ua
       let mb := fb.sigOf ub
       let qa := fa.ulpExpOf ua
       let qb := fb.ulpExpOf ub
       let qc := Min.min qa qb
       let A : Int := (if ua.sign then -1 else 1) * ((ma <<< (qa - qc).toNat : Nat) : Int)
       let B : Int := (if ub.sign then -1 else 1) * ((mb <<< (qb - qc).toNat : Nat) : Int)
       let S := A + B
       if S = 0 then
         let zsign : Bool :=
           if ma = 0 && mb = 0 && ua.sign == ub.sign then ua.sign
           else rm = RoundingDirection.roundTowardNegative
         (dst.pack zsign 0 0, {})
       else
         dst.roundPack sp rm (S < 0) S.natAbs qc) :=
  roundedResultOf_ite_zero sp dst rm
    (by rw [valR_eq_sigOf fa hfa, valR_eq_sigOf fb hfb, alignedSum_mul_zpow])
    (zeroSumSign_eq rm _ _ _ _ _ _)

theorem additionSpecOf_addition (sp : Specialization) (hsp : Specialization.Valid sp)
    (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    AdditionSpecOf sp fa fb dst rm a b (Format.addition sp fa fb dst rm a b) := by
  have hnan := (hsp.propagateNaN .addition dst [(fa, a), (fb, b)]).2
  unfold AdditionSpecOf arithSumOf Format.addition
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack, arithIsInf_eq, arithIsInf_eq]
  by_cases hn : (isNaN fa a || isNaN fb b) = true
  · simp only [hn, ↓reduceIte]; exact ⟨hnan, by trivial, by trivial⟩
  · have hna : isNaN fa a = false := by simp_all
    have hnb : isNaN fb b = false := by simp_all
    rw [arithSign_eq fa hna, arithSign_eq fb hnb]
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    have hinf := pack_expMax_lt dst (fa.unpack a).sign
    have hinf' := pack_expMax_lt dst (fb.unpack b).sign
    cases hia : fa.isInfU (fa.unpack a) <;> cases hib : fb.isInfU (fb.unpack b)
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      have h := roundedResultOf_finite_addition sp fa fb dst rm
        (isFinite_of_not_isNaN_not_isInfU fa hna hia) (isFinite_of_not_isNaN_not_isInfU fb hnb hib)
      exact ⟨h.1, h⟩
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hinf', classify_pack_infinity dst _, by trivial⟩
    · simp only [Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hinf, classify_pack_infinity dst _, by trivial⟩
    · simp only [Bool.true_and, ↓reduceIte]
      split_ifs
      · exact ⟨hnan, by trivial, by trivial⟩
      · exact ⟨hinf, classify_pack_infinity dst _, by trivial⟩

section FlipSign

variable (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width)
include hx

theorem unpack_flipSign : fmt.unpack (fmt.flipSign x) = { fmt.unpack x with sign := !(fmt.unpack x).sign } := by
  rw [flipSign_eq_withSign fmt hx, unpack_withSign]

theorem isNaN_flipSign : isNaN fmt (fmt.flipSign x) = isNaN fmt x := by
  rw [← isNaNU_unpack, ← isNaNU_unpack, unpack_flipSign fmt hx]; rfl

theorem isSignalingNaN_flipSign : isSignalingNaN fmt (fmt.flipSign x) = isSignalingNaN fmt x := by
  rw [← isSNaNU_unpack, ← isSNaNU_unpack, unpack_flipSign fmt hx]; rfl

theorem arithIsInf_flipSign : arithIsInf fmt (fmt.flipSign x) = arithIsInf fmt x := by
  rw [arithIsInf_eq, arithIsInf_eq, unpack_flipSign fmt hx]; rfl

theorem arithSign_flipSign (hn : isNaN fmt x = false) :
    arithSign fmt (fmt.flipSign x) = !arithSign fmt x := by
  rw [arithSign_eq fmt hn, arithSign_eq fmt (by rw [isNaN_flipSign fmt hx]; exact hn),
    unpack_flipSign fmt hx]

theorem valR_flipSign : valR fmt (fmt.flipSign x) = -valR fmt x := by
  rw [flipSign_eq_withSign fmt hx, valR_withSign]; simp

end FlipSign

theorem subtractionSpecOf_subtraction (sp : Specialization) (hsp : Specialization.Valid sp)
    (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) (hb : b < 2 ^ fb.width) :
    SubtractionSpecOf sp fa fb dst rm a b (Format.subtraction sp fa fb dst rm a b) := by
  have hnan := (hsp.propagateNaN .subtraction dst [(fa, a), (fb, b)]).2
  have hadd := additionSpecOf_addition sp hsp fa fb dst rm a (fb.flipSign b)
  unfold SubtractionSpecOf arithSumOf Format.subtraction
  unfold AdditionSpecOf arithSumOf at hadd
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack]
  rw [isNaN_flipSign fb hb, isSignalingNaN_flipSign fb hb, arithIsInf_flipSign fb hb,
    valR_flipSign fb hb] at hadd
  by_cases hn : (isNaN fa a || isNaN fb b) = true
  · simp only [hn, ↓reduceIte]; exact ⟨hnan, by trivial, by trivial⟩
  · have hna : isNaN fa a = false := by simp_all
    have hnb : isNaN fb b = false := by simp_all
    rw [arithSign_flipSign fb hb hnb] at hadd
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at hadd ⊢
    rw [arithIsInf_eq, arithIsInf_eq, arithSign_eq fa hna, arithSign_eq fb hnb] at hadd ⊢
    generalize fa.isInfU (fa.unpack a) = ia at hadd ⊢
    generalize fb.isInfU (fb.unpack b) = ib at hadd ⊢
    generalize (fa.unpack a).sign = sa at hadd ⊢
    generalize (fb.unpack b).sign = sb at hadd ⊢
    cases ia <;> cases ib <;> cases sa <;> cases sb <;>
      simp only [Bool.and_false, Bool.and_true, Bool.false_eq_true,
        Bool.not_false, Bool.not_true, bne_self_eq_false, Bool.bne_true, Bool.bne_false,
        beq_self_eq_true, Bool.false_beq, Bool.true_beq, ↓reduceIte] at hadd ⊢ <;>
      first | exact hadd | exact ⟨hnan, by trivial, by trivial⟩

theorem multiplicationSpecOf_multiplication (sp : Specialization) (hsp : Specialization.Valid sp)
    (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    MultiplicationSpecOf sp fa fb dst rm a b (Format.multiplication sp fa fb dst rm a b) := by
  have hnan := (hsp.propagateNaN .multiplication dst [(fa, a), (fb, b)]).2
  unfold MultiplicationSpecOf Format.multiplication
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack, arithIsInf_eq, arithIsInf_eq,
    arithIsZero_eq, arithIsZero_eq]
  by_cases hn : (isNaN fa a || isNaN fb b) = true
  · simp only [hn, ↓reduceIte]; exact ⟨hnan, by trivial, by trivial⟩
  · have hna : isNaN fa a = false := by simp_all
    have hnb : isNaN fb b = false := by simp_all
    rw [arithSign_eq fa hna, arithSign_eq fb hnb]
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    have hinf := pack_expMax_lt dst ((fa.unpack a).sign != (fb.unpack b).sign)
    cases hia : fa.isInfU (fa.unpack a) <;> cases hib : fb.isInfU (fb.unpack b)
    · have hfa := isFinite_of_not_isNaN_not_isInfU fa hna hia
      have hfb := isFinite_of_not_isNaN_not_isInfU fb hnb hib
      simp only [Bool.false_and, Bool.and_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      have h : RoundedResultOf sp dst rm (valR fa a * valR fb b)
          ((fa.unpack a).sign != (fb.unpack b).sign)
          (if (isZeroU (fa.unpack a) || isZeroU (fb.unpack b)) = true then
            (dst.pack ((fa.unpack a).sign != (fb.unpack b).sign) 0 0, {})
          else dst.roundPack sp rm ((fa.unpack a).sign != (fb.unpack b).sign)
            (fa.sigOf (fa.unpack a) * fb.sigOf (fb.unpack b))
            (fa.ulpExpOf (fa.unpack a) + fb.ulpExpOf (fb.unpack b))) := by
        split_ifs with hz
        · have h0 : valR fa a * valR fb b = 0 := by
            rcases Bool.or_eq_true_iff.mp hz with hz | hz
            · rw [valR_eq_zero_of_isZeroU fa hz, zero_mul]
            · rw [valR_eq_zero_of_isZeroU fb hz, mul_zero]
          rw [h0]; exact roundedResultOf_zero sp dst rm _
        · have hza : isZeroU (fa.unpack a) = false := by simp_all
          have hzb : isZeroU (fb.unpack b) = false := by simp_all
          rw [valR_mul_valR fa fb hfa hfb]
          exact roundPack_spec sp dst rm _ _ _
            (Nat.mul_pos (sigOf_pos fa hza) (sigOf_pos fb hzb)) _
      exact ⟨h.1, h⟩
    · cases isZeroU (fa.unpack a) <;>
        simp only [isZeroU_eq_false_of_isInfU fb hib, Bool.and_false, Bool.and_true,
          Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte] <;>
        first
        | exact ⟨hnan, by trivial, by trivial⟩
        | exact ⟨hinf, classify_pack_infinity dst _, by trivial⟩
    · cases isZeroU (fb.unpack b) <;>
        simp only [isZeroU_eq_false_of_isInfU fa hia, Bool.and_false, Bool.and_true,
          Bool.or_false, Bool.false_eq_true, ↓reduceIte] <;>
        first
        | exact ⟨hnan, by trivial, by trivial⟩
        | exact ⟨hinf, classify_pack_infinity dst _, by trivial⟩
    · simp only [isZeroU_eq_false_of_isInfU fa hia, isZeroU_eq_false_of_isInfU fb hib,
        Bool.and_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hinf, classify_pack_infinity dst _, by trivial⟩

theorem softfloat_addition_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa fb dst rm a b, a < 2 ^ fa.width → b < 2 ^ fb.width →
      AdditionSpecOf sp fa fb dst rm a b ((softfloat sp).addition fa fb dst rm a b) :=
  fun fa fb dst rm a b _ _ => additionSpecOf_addition sp hsp fa fb dst rm a b

theorem softfloat_subtraction_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa fb dst rm a b, a < 2 ^ fa.width → b < 2 ^ fb.width →
      SubtractionSpecOf sp fa fb dst rm a b ((softfloat sp).subtraction fa fb dst rm a b) :=
  fun fa fb dst rm a b _ hb => subtractionSpecOf_subtraction sp hsp fa fb dst rm a b hb

theorem softfloat_multiplication_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa fb dst rm a b, a < 2 ^ fa.width → b < 2 ^ fb.width →
      MultiplicationSpecOf sp fa fb dst rm a b ((softfloat sp).multiplication fa fb dst rm a b) :=
  fun fa fb dst rm a b _ _ => multiplicationSpecOf_multiplication sp hsp fa fb dst rm a b

section

variable {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}

theorem arithSumOf_unique {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat} {sb : Bool}
    {vb : ℝ} {nan : Nat} (h₁ : arithSumOf sp fa fb dst rm a b sb vb nan r₁)
    (h₂ : arithSumOf sp fa fb dst rm a b sb vb nan r₂) : r₁ = r₂ := by
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ <;> uniq_close

theorem additionSpecOf_unique {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat}
    (h₁ : AdditionSpecOf sp fa fb dst rm a b r₁) (h₂ : AdditionSpecOf sp fa fb dst rm a b r₂) :
    r₁ = r₂ :=
  arithSumOf_unique h₁ h₂

theorem subtractionSpecOf_unique {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat}
    (h₁ : SubtractionSpecOf sp fa fb dst rm a b r₁)
    (h₂ : SubtractionSpecOf sp fa fb dst rm a b r₂) : r₁ = r₂ :=
  arithSumOf_unique h₁ h₂

theorem multiplicationSpecOf_unique {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat}
    (h₁ : MultiplicationSpecOf sp fa fb dst rm a b r₁)
    (h₂ : MultiplicationSpecOf sp fa fb dst rm a b r₂) : r₁ = r₂ := by
  unfold MultiplicationSpecOf at h₁ h₂; dsimp only at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ <;> uniq_close

end

end SoftFloat.Proof
