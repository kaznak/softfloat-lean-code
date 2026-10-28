/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.ConvertFormat
import SoftFloat.Core.Proof.ConvertToInteger

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem sigOf_lt_two_pow_sigBits (fmt : Format) (u : Unpacked) (hf : u.fracField < 2 ^ fmt.fracBits) :
    fmt.sigOf u < 2 ^ fmt.sigBits := by
  have h2 : 2 ^ fmt.sigBits = 2 * 2 ^ fmt.fracBits := by
    rw [sigBits_eq_fracBits_add_one, pow_succ]; ring
  unfold Format.sigOf; split_ifs <;> omega

theorem expField_lt_expMax_of_isFinite (fmt : Format) {a : Nat} (hf : IsFinite fmt a) :
    (fmt.unpack a).expField < fmt.expMax := by
  have h1 := (isFinite_iff fmt a).1 hf
  have h2 := unpack_expField_lt fmt a
  have h3 := expMax_add_one fmt
  omega

theorem integralPartOf_zero (rm : RoundingDirection) (s : Bool) : integralPartOf rm s 0 = 0 := by
  simp [integralPartOf, roundAbs_zero]

theorem integralPartOf_signed (rm : RoundingDirection) (s : Bool) (m : ℕ) (q : ℤ) :
    integralPartOf rm s ((if s then -1 else 1) * (m : ℝ) * 2 ^ q)
      = (if s then -1 else 1) * roundAbs rm s ((m : ℝ) * 2 ^ q) := by
  unfold integralPartOf; rw [abs_signed]

theorem roundAt_zero_eq_roundAbs (rm : RoundingDirection) (s : Bool) (m : ℕ) (q : ℤ) :
    ((roundAt rm s m q 0 : ℕ) : ℤ) = roundAbs rm s ((m : ℝ) * 2 ^ q) := by
  rw [roundAt_eq_roundAbs]; simp

theorem roundAt_zero_mul_eq_iff (rm : RoundingDirection) (s : Bool) (m : ℕ) (q : ℤ) :
    (roundAt rm s m q 0 : ℝ) = m * 2 ^ q ↔ inexactAt m q 0 = false := by
  rw [← roundAt_mul_eq_iff rm s m q 0]; simp

theorem roundToIntegral_spec_of_finite (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (exact : Bool) (hbias : fmt.fracBits ≤ fmt.bias) {a : Nat} (ha : a < 2 ^ fmt.width)
    (hf : IsFinite fmt a) (hz : isZeroU (fmt.unpack a) = false) :
    let s := (fmt.unpack a).sign
    let n := integralPartOf rm s (valR fmt a)
    let r := fmt.roundToIntegral sp rm exact a
    r.1 < 2 ^ fmt.width ∧ IsFinite fmt r.1 ∧ valR fmt r.1 = n
      ∧ (n = 0 → classify fmt r.1 = .zero s)
      ∧ integralFlagsOf exact ((n : ℝ) ≠ valR fmt a) r.2 := by
  intro s n r
  have hm := sigOf_pos fmt hz
  have hmlt := sigOf_lt_two_pow_sigBits fmt (fmt.unpack a) (unpack_fracField_lt fmt a)
  have hv : valR fmt a = (if s then -1 else 1) * ((fmt.sigOf (fmt.unpack a) : ℕ) : ℝ)
      * 2 ^ fmt.ulpExpOf (fmt.unpack a) := valR_eq_sigOf fmt hf
  have hv0 : valR fmt a ≠ 0 := by rw [hv]; exact signed_ne_zero s _ _ hm
  have hn : n = (if s then -1 else 1) * roundAbs rm s
      ((fmt.sigOf (fmt.unpack a) : ℝ) * 2 ^ fmt.ulpExpOf (fmt.unpack a)) := by
    simp only [n]; rw [hv]; exact integralPartOf_signed rm s _ _
  have hE := expField_lt_expMax_of_isFinite fmt hf
  have hb1 := one_le_bias fmt
  have hf1 := one_le_fracBits fmt
  simp only [r, Format.roundToIntegral, isNaNU_eq_false_of_isFinite fmt hf, hz, not_le.mpr hE,
    Bool.false_eq_true, ↓reduceIte]
  by_cases hbig : fmt.bias + fmt.fracBits ≤ (fmt.unpack a).expField
  · simp only [hbig, ↓reduceIte]
    have hq : 0 ≤ fmt.ulpExpOf (fmt.unpack a) := by
      unfold Format.ulpExpOf; split_ifs <;> omega
    have hk := natCast_mul_zpow_nonneg (fmt.sigOf (fmt.unpack a)) hq
    have hnv : (n : ℝ) = valR fmt a := by
      rw [hn, hk, roundAbs_natCast, hv, mul_assoc, hk]
      generalize fmt.sigOf (fmt.unpack a) <<< (fmt.ulpExpOf (fmt.unpack a)).toNat = k
      split_ifs <;> simp
    refine ⟨ha, hf, hnv.symm, fun h0 => absurd (by rw [← hnv, h0]; simp) hv0, ?_⟩
    simp [integralFlagsOf, hnv]
  · simp only [hbig, ↓reduceIte]
    have hq : fmt.ulpExpOf (fmt.unpack a) < 0 := by
      unfold Format.ulpExpOf; split_ifs <;> omega
    set m := fmt.sigOf (fmt.unpack a) with hm_def
    set q := fmt.ulpExpOf (fmt.unpack a) with hq_def
    have hzr : (let d := 2 ^ (-q).toNat
        if roundIncr rm s (m / d) (m % d) d then m / d + 1 else m / d) = roundAt rm s m q 0 := by
      simp [roundAt, not_le.mpr hq]
    have hrem : (m % 2 ^ (-q).toNat != 0) = inexactAt m q 0 := by
      simp [inexactAt, not_le.mpr hq]
    simp only at hzr
    rw [hzr, hrem]
    set z := roundAt rm s m q 0 with hz_def
    have hnz : n = (if s then -1 else 1) * (z : ℤ) := by
      rw [hn, hz_def, roundAt_zero_eq_roundAbs]
    have hch : ((n : ℝ) ≠ valR fmt a) ↔ inexactAt m q 0 = true := by
      have key := roundAt_zero_mul_eq_iff rm s m q
      rw [← hz_def] at key
      have h1 : (n : ℝ) = (if s then -1 else 1) * (z : ℝ) := by rw [hnz]; split_ifs <;> simp
      have h2 : (if s then -1 else 1 : ℝ) ≠ 0 := by split_ifs <;> norm_num
      rw [h1, hv, mul_assoc _ (m : ℝ), ne_eq, mul_right_inj' h2, key]
      simp
    have hflags : integralFlagsOf exact ((n : ℝ) ≠ valR fmt a)
        { inexact := exact && inexactAt m q 0 } := by
      simp [integralFlagsOf, hch]
    by_cases hz0 : z = 0
    · simp only [hz0, ↓reduceIte]
      have hn0 : n = 0 := by rw [hnz, hz0]; simp
      refine ⟨pack_lt fmt s (by positivity) (by positivity),
        isFinite_pack fmt s (Nat.pos_of_ne_zero (expMax_ne_zero fmt)) (by positivity),
        by rw [valR_pack_zero, hn0]; simp, fun _ => classify_pack_zero fmt s, ?_⟩
      exact hflags
    · simp only [hz0, ↓reduceIte]
      have hzle : z ≤ 2 ^ fmt.fracBits := by
        apply roundAt_le
        have h2 : (2 : ℝ) ^ fmt.sigBits = 2 * 2 ^ fmt.fracBits := by
          rw [sigBits_eq_fracBits_add_one, pow_succ]; ring
        have hmR : (m : ℝ) < 2 ^ fmt.sigBits := by exact_mod_cast hmlt
        have hqR : (2 : ℝ) ^ q ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        have : (m : ℝ) * 2 ^ q ≤ m * 2 ^ (-1 : ℤ) :=
          mul_le_mul_of_nonneg_left hqR (by positivity)
        rw [zpow_neg_one] at this
        simp only [zpow_zero, mul_one]
        linarith
      have hzlt : z < 2 ^ fmt.sigBits := lt_of_le_of_lt hzle
        (Nat.pow_lt_pow_right (by decide) (by rw [sigBits_eq_fracBits_add_one]; omega))
      have hE := expMax_eq_two_mul_bias_add_one fmt
      obtain ⟨hlt, hfin, hval, -⟩ := roundPack_exact_spec sp fmt rm s (q := 0)
        (Nat.pos_of_ne_zero hz0) hzlt (by unfold Format.minQ; omega) (by unfold emax; omega)
      refine ⟨hlt, hfin, by rw [hval, hnz]; push_cast; split_ifs <;> simp, ?_, hflags⟩
      intro h0; rw [hnz] at h0; split_ifs at h0 <;> omega

theorem roundToIntegral_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (exact : Bool) (hbias : fmt.fracBits ≤ fmt.bias) {a : Nat} (ha : a < 2 ^ fmt.width) :
    RoundToIntegralSpecOf sp fmt rm exact a (fmt.roundToIntegral sp rm exact a) := by
  have hnan := isNaNU_unpack fmt a
  have hsnan := isSNaNU_unpack fmt a
  have hfin := roundToIntegral_spec_of_finite sp fmt rm exact hbias ha
  unfold RoundToIntegralSpecOf
  cases hc : classify fmt a with
  | quietNaN =>
    have h : isNaN fmt a = true := by simp [isNaN, hc]
    simp [Format.roundToIntegral, hnan, hsnan, h]
  | signalingNaN =>
    have h : isNaN fmt a = true := by simp [isNaN, hc]
    simp [Format.roundToIntegral, hnan, hsnan, h]
  | infinity t =>
    obtain ⟨hi, _⟩ := (classify_eq_infinity_iff fmt a t).1 hc
    have h : isNaN fmt a = false := by simp [isNaN, hc]
    unfold Format.isInfU at hi
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    have hz : isZeroU (fmt.unpack a) = false := by
      unfold Format.isZeroU; simp [hi.1, expMax_ne_zero]
    simp only [Format.roundToIntegral, hnan, h, hz, hi.1, le_refl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨ha, hc, rfl⟩
  | zero t =>
    obtain ⟨hz, hs⟩ := (classify_eq_zero_iff fmt a t).1 hc
    have hf : IsFinite fmt a := by simp [IsFinite, hc]
    have hv : valR fmt a = 0 := (valR_eq_zero_iff fmt a).2 (Or.inr ⟨t, hc⟩)
    simp only [Format.roundToIntegral, isNaNU_eq_false_of_isFinite fmt hf, hz,
      Bool.false_eq_true, ↓reduceIte]
    rw [hv, integralPartOf_zero]
    exact ⟨ha, hf, by simp, fun _ => hc, by simp [integralFlagsOf]⟩
  | normal t =>
    obtain ⟨hn, hs⟩ := (classify_eq_normal_iff fmt a t).1 hc
    have hz : isZeroU (fmt.unpack a) = false := by
      unfold Format.isNormalU at hn; unfold Format.isZeroU
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.1]
    rw [← hs]; exact hfin (by simp [IsFinite, hc]) hz
  | subnormal t =>
    obtain ⟨hn, hs⟩ := (classify_eq_subnormal_iff fmt a t).1 hc
    have hz : isZeroU (fmt.unpack a) = false := by
      unfold Format.isSubnormalU at hn; unfold Format.isZeroU
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.2]
    rw [← hs]; exact hfin (by simp [IsFinite, hc]) hz

theorem softfloat_roundToIntegral_spec (sp : Specialization) :
    ∀ fmt rm exact a, a < 2 ^ fmt.width →
      RoundToIntegralSpecOf sp fmt rm exact a ((softfloat sp).roundToIntegral fmt rm exact a) :=
  fun fmt rm exact _ ha => roundToIntegral_spec sp fmt rm exact fmt.fracBits_le_bias ha

theorem roundToIntegralSpecOf_unique {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}
    {fmt : Format} {rm : RoundingDirection} {exact : Bool}
    {a : Nat} (h₁ : RoundToIntegralSpecOf sp fmt rm exact a r₁)
    (h₂ : RoundToIntegralSpecOf sp fmt rm exact a r₂) : r₁ = r₂ := by
  unfold RoundToIntegralSpecOf convertExactSpecialOf at h₁ h₂
  cases hc : classify fmt a <;> simp only [hc] at h₁ h₂
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (eq_of_classify_eq_infinity _ h₁.1 h₂.1 h₁.2.1 h₂.2.1)
      (h₁.2.2.trans h₂.2.2.symm)
  all_goals
    obtain ⟨hw₁, hf₁, hv₁, hz₁, hl₁⟩ := h₁
    obtain ⟨hw₂, hf₂, hv₂, hz₂, hl₂⟩ := h₂
    refine Prod.ext ?_ (integralFlagsOf_unique hl₁ hl₂)
    by_cases h0 : valR fmt r₁.1 = 0
    · rw [hv₁] at h0
      have h0' := Int.cast_eq_zero.1 h0
      exact eq_of_classify_eq_zero fmt hw₁ hw₂ (hz₁ h0') (hz₂ h0')
    · exact eq_of_valR_eq fmt hw₁ hw₂ hf₁ hf₂ (hv₁.trans hv₂.symm) h0

end SoftFloat.Proof
