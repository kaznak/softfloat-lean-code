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

theorem sign_ne_of_signed_add_eq_zero {s t : Bool} {p c : ℕ} (hp : p ≠ 0)
    (h : (if s then -1 else 1) * (p : ℤ) + (if t then -1 else 1) * (c : ℤ) = 0) : s ≠ t := by
  rintro rfl
  cases s <;> simp at h <;> omega

theorem fusedMultiplyAdd_finite_spec (sp : Specialization) (fa fb fc dst : Format)
    (rm : RoundingDirection) {a b c : Nat}
    (hna : fa.isNaNU (fa.unpack a) = false) (hnb : fb.isNaNU (fb.unpack b) = false)
    (hnc : fc.isNaNU (fc.unpack c) = false)
    (hia : fa.isInfU (fa.unpack a) = false) (hib : fb.isInfU (fb.unpack b) = false)
    (hic : fc.isInfU (fc.unpack c) = false) :
    RoundedResultOf sp dst rm (valR fa a * valR fb b + valR fc c)
      (arithZeroSumNegative rm ((fa.unpack a).sign != (fb.unpack b).sign) (fc.unpack c).sign)
      (Format.fusedMultiplyAdd sp fa fb fc dst rm a b c) := by
  rw [valR_mul_valR fa fb
      (isFinite_of_not_isNaN_not_isInfU fa ((isNaNU_unpack fa a).symm.trans hna) hia)
      (isFinite_of_not_isNaN_not_isInfU fb ((isNaNU_unpack fb b).symm.trans hnb) hib),
    valR_eq_sigOf fc (isFinite_of_not_isNaN_not_isInfU fc ((isNaNU_unpack fc c).symm.trans hnc) hic)]
  simp only [Format.fusedMultiplyAdd, hna, hnb, hnc, hia, hib, hic, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte]
  generalize ((fa.unpack a).sign != (fb.unpack b).sign) = s
  generalize (fc.unpack c).sign = t
  generalize fa.sigOf (fa.unpack a) * fb.sigOf (fb.unpack b) = mp
  generalize fa.ulpExpOf (fa.unpack a) + fb.ulpExpOf (fb.unpack b) = qp
  generalize fc.sigOf (fc.unpack c) = mc
  generalize fc.ulpExpOf (fc.unpack c) = qc
  by_cases hmp : mp = 0
  · subst hmp
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, ↓reduceIte]
    by_cases hmc : mc = 0
    · subst hmc
      have hz : arithZeroSumNegative rm s t
          = (if (s == t) = true then t else decide (rm = .roundTowardNegative)) := by
        cases s <;> cases t <;> rfl
      simp only [Nat.cast_zero, mul_zero, zero_mul, ↓reduceIte]
      rw [hz]; exact roundedResultOf_zero sp dst rm _
    · simp only [hmc, ↓reduceIte]; exact roundPack_spec sp dst rm t mc qc (Nat.pos_of_ne_zero hmc) _
  · simp only [hmp, ↓reduceIte]
    rw [← alignedSum_mul_zpow]
    have hp : mp <<< (qp - min qp qc).toNat ≠ 0 := by
      rw [Nat.shiftLeft_eq]; exact Nat.mul_ne_zero hmp (by positivity)
    generalize hS : (if s = true then -1 else 1) * ((mp <<< (qp - min qp qc).toNat : ℕ) : ℤ)
      + (if t = true then -1 else 1) * ((mc <<< (qc - min qp qc).toNat : ℕ) : ℤ) = S
    by_cases hS0 : S = 0
    · have hst := sign_ne_of_signed_add_eq_zero hp (hS.trans hS0)
      subst hS0
      simp only [Int.cast_zero, zero_mul, arithZeroSumNegative, hst, ↓reduceIte]
      exact roundedResultOf_zero sp dst rm _
    · simp only [hS0, ↓reduceIte]
      rw [intCast_eq_signed_natAbs]
      exact roundPack_spec sp dst rm _ _ _ (Int.natAbs_pos.mpr hS0) _

private theorem zeroTimesInf_eq (fa fb : Format) (a b : Nat) :
    ((fa.isInfU (fa.unpack a) && isZeroU (fb.unpack b))
      || (isZeroU (fa.unpack a) && fb.isInfU (fb.unpack b)))
      = ((fa.isInfU (fa.unpack a) || fb.isInfU (fb.unpack b))
        && (isZeroU (fa.unpack a) || isZeroU (fb.unpack b))) := by
  have ha := @isZeroU_eq_false_of_isInfU fa (fa.unpack a)
  have hb := @isZeroU_eq_false_of_isInfU fb (fb.unpack b)
  cases hia : fa.isInfU (fa.unpack a) <;> cases hib : fb.isInfU (fb.unpack b) <;> simp_all

theorem fusedMultiplyAddSpecOf_fusedMultiplyAdd (sp : Specialization)
    (hsp : Specialization.Valid sp) (fa fb fc dst : Format) (rm : RoundingDirection) (a b c : Nat) :
    FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c
      (Format.fusedMultiplyAdd sp fa fb fc dst rm a b c) := by
  have hnan : _ < 2 ^ dst.width := (hsp.propagateNaN .fusedMultiplyAdd dst [(fa, a), (fb, b), (fc, c)]).2
  have hpinf := pack_expMax_lt dst
  unfold FusedMultiplyAddSpecOf
  simp only [arithIsInf_eq, arithIsZero_eq, ← isNaNU_unpack, ← isSNaNU_unpack,
    zeroTimesInf_eq]
  by_cases hab : (fa.isNaNU (fa.unpack a) || fb.isNaNU (fb.unpack b)) = true
  · simp only [Format.fusedMultiplyAdd, hab, ↓reduceIte]
    refine ⟨hnan, ?_⟩
    simp
  have hna : fa.isNaNU (fa.unpack a) = false := by simp_all
  have hnb : fb.isNaNU (fb.unpack b) = false := by simp_all
  rw [arithSign_eq fa (by rw [← isNaNU_unpack]; exact hna),
    arithSign_eq fb (by rw [← isNaNU_unpack]; exact hnb)]
  by_cases hnc : fc.isNaNU (fc.unpack c) = true
  · by_cases hI : (fa.isInfU (fa.unpack a) || fb.isInfU (fb.unpack b)) = true
    · by_cases hZ : (isZeroU (fa.unpack a) || isZeroU (fb.unpack b)) = true
      · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc, hI, hZ, Bool.or_false, Bool.and_self,
          Bool.false_eq_true, ↓reduceIte]
        cases fc.isSNaNU (fc.unpack c) <;> simp [hnan]
      · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc, hI, hZ, Bool.or_false, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
        simp [hnan]
    · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc, hI, Bool.or_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      simp [hnan]
  have hnc' : fc.isNaNU (fc.unpack c) = false := by simp_all
  rw [arithSign_eq fc (by rw [← isNaNU_unpack]; exact hnc')]
  by_cases hI : (fa.isInfU (fa.unpack a) || fb.isInfU (fb.unpack b)) = true
  · by_cases hZ : (isZeroU (fa.unpack a) || isZeroU (fb.unpack b)) = true
    · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc', hI, hZ, Bool.or_false, Bool.and_self,
        Bool.false_eq_true, ↓reduceIte]
      simp [hnan]
    · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc', hI, hZ, Bool.or_false, Bool.and_false,
        Bool.false_eq_true, ↓reduceIte]
      cases fc.isInfU (fc.unpack c) <;> cases (fa.unpack a).sign <;> cases (fb.unpack b).sign <;>
        cases (fc.unpack c).sign <;> simp [hnan, hpinf, classify_pack_infinity]
  · have hia : fa.isInfU (fa.unpack a) = false := by simp_all
    have hib : fb.isInfU (fb.unpack b) = false := by simp_all
    by_cases hic : fc.isInfU (fc.unpack c) = true
    · simp only [Format.fusedMultiplyAdd, hna, hnb, hnc', hia, hib, hic, Bool.or_false,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      simp [hpinf, classify_pack_infinity]
    · have hic' : fc.isInfU (fc.unpack c) = false := by simp_all
      have hfin := fusedMultiplyAdd_finite_spec sp fa fb fc dst rm hna hnb hnc' hia hib hic'
      simp only [hna, hnb, hnc', hia, hib, hic', Bool.or_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨hfin.1, hfin⟩

theorem softfloat_fusedMultiplyAdd_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa fb fc dst rm a b c, a < 2 ^ fa.width → b < 2 ^ fb.width → c < 2 ^ fc.width →
      FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c
        ((softfloat sp).fusedMultiplyAdd fa fb fc dst rm a b c) :=
  fun fa fb fc dst rm a b c _ _ _ =>
    fusedMultiplyAddSpecOf_fusedMultiplyAdd sp hsp fa fb fc dst rm a b c

theorem fusedMultiplyAddSpecOf_unique {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}
    {fa fb fc dst : Format} {rm : RoundingDirection}
    {a b c : Nat} (h₁ : FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c r₁)
    (h₂ : FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c r₂) : r₁ = r₂ := by
  unfold FusedMultiplyAddSpecOf at h₁ h₂; dsimp only at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ <;> uniq_close

end SoftFloat.Proof
