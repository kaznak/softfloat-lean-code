/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Sticky

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem div_bracket (ma mb k : ℕ) (qa qb : ℤ) (hmb : 0 < mb) :
    (((ma <<< k) / mb : ℕ) : ℝ) * 2 ^ (qa - qb - k) ≤ (ma * 2 ^ qa) / (mb * 2 ^ qb) ∧
      (ma * 2 ^ qa) / (mb * 2 ^ qb) < ((((ma <<< k) / mb : ℕ) : ℝ) + 1) * 2 ^ (qa - qb - k) ∧
      ((ma <<< k) % mb = 0 ↔
        (ma * 2 ^ qa) / (mb * 2 ^ qb) = (((ma <<< k) / mb : ℕ) : ℝ) * 2 ^ (qa - qb - k)) := by
  set Q := (ma <<< k) / mb
  set rem := (ma <<< k) % mb
  have hmbR : (0 : ℝ) < mb := by exact_mod_cast hmb
  have hrem : rem < mb := Nat.mod_lt _ hmb
  have hremR : (rem : ℝ) < mb := by exact_mod_cast hrem
  have hN : ((ma <<< k : ℕ) : ℝ) = Q * mb + rem := by
    have := Nat.div_add_mod (ma <<< k) mb
    rw [mul_comm] at this
    exact_mod_cast this.symm
  have hv : ((ma : ℝ) * 2 ^ qa) / (mb * 2 ^ qb) = (Q + rem / mb) * 2 ^ (qa - qb - k) := by
    have hk : ((ma <<< k : ℕ) : ℝ) = ma * 2 ^ (k : ℤ) := by
      rw [Nat.shiftLeft_eq]; push_cast; rw [zpow_natCast]
    have h1 : (Q : ℝ) + rem / mb = ma * 2 ^ (k : ℤ) / mb := by
      rw [← hk, hN]; field_simp
    rw [h1, zpow_sub₀ two_ne_zero, zpow_sub₀ two_ne_zero]
    field_simp
  have hp : (0 : ℝ) < 2 ^ (qa - qb - k) := by positivity
  have hf0 : (0 : ℝ) ≤ rem / mb := by positivity
  have hf1 : (rem : ℝ) / mb < 1 := (div_lt_one hmbR).2 hremR
  rw [hv]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  constructor
  · intro h; simp [h]
  · intro h
    have : (rem : ℝ) / mb * 2 ^ (qa - qb - k) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · rcases div_eq_zero_iff.1 h' with h'' | h''
      · exact_mod_cast h''
      · exact absurd h'' hmbR.ne'
    · exact absurd h' hp.ne'

theorem two_pow_le_shiftLeft_div (ma mb p : ℕ) (hma : 0 < ma) (hmb : 0 < mb) :
    2 ^ p ≤ (ma <<< (p + (Nat.log2 mb + 1))) / mb := by
  rw [Nat.le_div_iff_mul_le hmb, Nat.shiftLeft_eq, pow_add]
  have h1 : mb < 2 ^ (Nat.log2 mb + 1) := Nat.lt_log2_self
  calc 2 ^ p * mb ≤ 2 ^ p * 2 ^ (Nat.log2 mb + 1) := Nat.mul_le_mul_left _ h1.le
    _ ≤ ma * (2 ^ p * 2 ^ (Nat.log2 mb + 1)) := Nat.le_mul_of_pos_left _ hma

theorem sign_div_sign (sa sb : Bool) :
    (if sa then (-1 : ℝ) else 1) / (if sb then -1 else 1) = if (sa != sb) then -1 else 1 := by
  cases sa <;> cases sb <;> norm_num

theorem division_finite_spec (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection)
    (a b : ℕ) (zn : Bool) (hfa : IsFinite fa a) (hfb : IsFinite fb b)
    (hza : isZeroU (fa.unpack a) = false) (hzb : isZeroU (fb.unpack b) = false) :
    RoundedResultOf sp dst rm (valR fa a / valR fb b) zn
      (dst.roundPack sp rm ((fa.unpack a).sign != (fb.unpack b).sign)
        (2 * ((fa.sigOf (fa.unpack a) <<< (dst.sigBits + 2 + (Nat.log2 (fb.sigOf (fb.unpack b)) + 1)))
            / fb.sigOf (fb.unpack b))
          + (if (fa.sigOf (fa.unpack a) <<< (dst.sigBits + 2 + (Nat.log2 (fb.sigOf (fb.unpack b)) + 1)))
              % fb.sigOf (fb.unpack b) = 0 then 0 else 1))
        (fa.ulpExpOf (fa.unpack a) - fb.ulpExpOf (fb.unpack b)
          - ((dst.sigBits + 2 + (Nat.log2 (fb.sigOf (fb.unpack b)) + 1) : ℕ) : ℤ) - 1)) := by
  set ma := fa.sigOf (fa.unpack a)
  set mb := fb.sigOf (fb.unpack b)
  set k := dst.sigBits + 2 + (Nat.log2 mb + 1)
  have hma := sigOf_pos fa hza
  have hmb := sigOf_pos fb hzb
  obtain ⟨h1, h2, h3⟩ := div_bracket ma mb k (fa.ulpExpOf (fa.unpack a)) (fb.ulpExpOf (fb.unpack b))
    hmb
  have hval : valR fa a / valR fb b = (if ((fa.unpack a).sign != (fb.unpack b).sign) then -1 else 1)
      * ((ma * 2 ^ fa.ulpExpOf (fa.unpack a)) / (mb * 2 ^ fb.ulpExpOf (fb.unpack b))) := by
    rw [valR_eq_sigOf fa hfa, valR_eq_sigOf fb hfb, ← sign_div_sign, mul_assoc, mul_assoc,
      mul_div_mul_comm]
  rw [hval]
  refine roundedResultOf_roundPack_sticky sp dst rm _ _ _ _ _ zn h1 h2 (by split_ifs <;> omega)
    ?_ ?_
  · rw [← h3]; split_ifs <;> simp_all
  · have := two_pow_le_shiftLeft_div ma mb (dst.sigBits + 2) hma hmb
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) this

theorem divisionSpecOf_division (sp : Specialization) (hsp : Specialization.Valid sp)
    (fa fb dst : Format) (rm : RoundingDirection) (a b : ℕ) :
    DivisionSpecOf sp fa fb dst rm a b (Format.division sp fa fb dst rm a b) := by
  unfold DivisionSpecOf Format.division
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack, arithIsInf_eq,
    arithIsInf_eq, arithIsZero_eq, arithIsZero_eq]
  cases hna : isNaN fa a <;> cases hnb : isNaN fb b <;>
    simp only [Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rotate_left
  · exact ⟨(hsp.propagateNaN _ _ _).2, by simp⟩
  · exact ⟨(hsp.propagateNaN _ _ _).2, by simp⟩
  · exact ⟨(hsp.propagateNaN _ _ _).2, by simp⟩
  rw [arithSign_eq fa hna, arithSign_eq fb hnb]
  have hnan : sp.propagateNaN .division dst [(fa, a), (fb, b)] < 2 ^ dst.width :=
    (hsp.propagateNaN _ _ _).2
  cases hia : fa.isInfU (fa.unpack a) <;> cases hib : fb.isInfU (fb.unpack b) <;>
    cases hza : isZeroU (fa.unpack a) <;> cases hzb : isZeroU (fb.unpack b) <;>
    simp only [Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, isEncoding_iff]
  all_goals try first
    | (have := isInfU_eq_false_of_isZeroU fa hza; rw [hia] at this; exact absurd this (by decide))
    | (have := isInfU_eq_false_of_isZeroU fb hzb; rw [hib] at this; exact absurd this (by decide))
    | with_reducible exact ⟨hnan, trivial, trivial⟩
    | (refine ⟨?_, ?_, trivial⟩; with_reducible exact pack_expMax_lt _ _; exact classify_pack_infinity _ _)
    | (refine ⟨?_, ?_, trivial⟩; with_reducible exact pack_zero_lt _ _; exact classify_pack_zero _ _)
  · have hfa := isFinite_of_not_isNaN_not_isInfU fa hna hia
    have hfb := isFinite_of_not_isNaN_not_isInfU fb hnb hib
    have h := division_finite_spec sp fa fb dst rm a b
      ((fa.unpack a).sign != (fb.unpack b).sign) hfa hfb hza hzb
    exact ⟨h.1, h⟩
  · rw [valR_eq_zero_of_isZeroU fa hza, zero_div]
    exact ⟨pack_zero_lt _ _, roundedResultOf_zero sp dst rm _⟩

theorem softfloat_division_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa fb dst rm a b, a < 2 ^ fa.width → b < 2 ^ fb.width →
      DivisionSpecOf sp fa fb dst rm a b ((softfloat sp).division fa fb dst rm a b) :=
  fun fa fb dst rm a b _ _ => divisionSpecOf_division sp hsp fa fb dst rm a b

theorem divisionSpecOf_unique {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}
    {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat}
    (h₁ : DivisionSpecOf sp fa fb dst rm a b r₁) (h₂ : DivisionSpecOf sp fa fb dst rm a b r₂) :
    r₁ = r₂ := by
  unfold DivisionSpecOf at h₁ h₂; dsimp only at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ <;> uniq_close

end SoftFloat.Proof
