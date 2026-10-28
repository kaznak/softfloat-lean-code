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

theorem convertFormat_spec_of_finite (sp : Specialization) (src dst : Format)
    (rm : RoundingDirection) {a : Nat} (hf : IsFinite src a) (hz : isZeroU (src.unpack a) = false) :
    RoundedResultOf sp dst rm (valR src a) (src.unpack a).sign (src.convertFormat sp dst rm a) := by
  simp only [Format.convertFormat, isNaNU_eq_false_of_isFinite src hf,
    isInfU_eq_false_of_isFinite src hf, hz, Bool.false_eq_true, ↓reduceIte]
  rw [valR_eq_sigOf src hf]
  exact roundPack_spec sp dst rm _ _ _ (sigOf_pos src hz) _

theorem convertFormat_spec (sp : Specialization) (src dst : Format) (rm : RoundingDirection)
    (a : Nat) : ConvertFormatSpecOf sp src dst rm a (src.convertFormat sp dst rm a) := by
  have hnan := isNaNU_unpack src a
  have hsnan := isSNaNU_unpack src a
  unfold ConvertFormatSpecOf
  cases hc : classify src a with
  | quietNaN =>
    have h : isNaN src a = true := by simp [isNaN, hc]
    simp [Format.convertFormat, hnan, hsnan, h, convertNaNResultOf]
  | signalingNaN =>
    have h : isNaN src a = true := by simp [isNaN, hc]
    simp [Format.convertFormat, hnan, hsnan, h, convertNaNResultOf]
  | infinity t =>
    obtain ⟨hi, hs⟩ := (classify_eq_infinity_iff src a t).1 hc
    have h : isNaN src a = false := by simp [isNaN, hc]
    simp only [Format.convertFormat, hnan, h, hi, hs, Bool.false_eq_true, ↓reduceIte]
    exact ⟨pack_lt dst t (expMax_lt dst) (by positivity), classify_pack_infinity dst t, rfl⟩
  | zero t =>
    obtain ⟨hz, hs⟩ := (classify_eq_zero_iff src a t).1 hc
    have hf : IsFinite src a := by simp [IsFinite, hc]
    have hv : valR src a = 0 := (valR_eq_zero_iff src a).2 (Or.inr ⟨t, hc⟩)
    simp only [Format.convertFormat, isNaNU_eq_false_of_isFinite src hf,
      isInfU_eq_false_of_isFinite src hf, hz, hs, Bool.false_eq_true, ↓reduceIte]
    rw [hv]; exact roundedResultOf_zero sp dst rm t
  | normal t =>
    obtain ⟨hn, hs⟩ := (classify_eq_normal_iff src a t).1 hc
    have hz : isZeroU (src.unpack a) = false := by
      unfold Format.isNormalU at hn; unfold Format.isZeroU
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.1]
    rw [← hs]; exact convertFormat_spec_of_finite sp src dst rm (by simp [IsFinite, hc]) hz
  | subnormal t =>
    obtain ⟨hn, hs⟩ := (classify_eq_subnormal_iff src a t).1 hc
    have hz : isZeroU (src.unpack a) = false := by
      unfold Format.isSubnormalU at hn; unfold Format.isZeroU
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.2]
    rw [← hs]; exact convertFormat_spec_of_finite sp src dst rm (by simp [IsFinite, hc]) hz

theorem softfloat_convertFormat_spec (sp : Specialization) :
    ∀ src dst rm a, a < 2 ^ src.width →
      ConvertFormatSpecOf sp src dst rm a ((softfloat sp).convertFormat src dst rm a) :=
  fun src dst rm a _ => convertFormat_spec sp src dst rm a

theorem convertFromInt_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (v : Int) :
    ConvertFromIntSpecOf sp fmt rm v (fmt.convertFromInt sp rm v) := by
  unfold ConvertFromIntSpecOf Format.convertFromInt
  split_ifs with hv
  · subst hv; simpa using roundedResultOf_zero sp fmt rm false
  · rw [← mul_one (v : ℝ), ← zpow_zero (2 : ℝ), intCast_eq_signed_natAbs v]
    exact roundPack_spec sp fmt rm _ _ _ (Int.natAbs_pos.mpr hv) _

theorem softfloat_convertFromInt_spec (sp : Specialization) :
    ∀ fmt rm v, ConvertFromIntSpecOf sp fmt rm v ((softfloat sp).convertFromInt fmt rm v) :=
  convertFromInt_spec sp

section

variable {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}

theorem convertFormatSpecOf_unique {src dst : Format} {rm : RoundingDirection} {a : Nat}
    (h₁ : ConvertFormatSpecOf sp src dst rm a r₁) (h₂ : ConvertFormatSpecOf sp src dst rm a r₂) :
    r₁ = r₂ := by
  unfold ConvertFormatSpecOf convertNaNResultOf convertExactSpecialOf at h₁ h₂
  cases hc : classify src a <;> simp only [hc] at h₁ h₂
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (eq_of_classify_eq_infinity _ h₁.1 h₂.1 h₁.2.1 h₂.2.1)
      (h₁.2.2.trans h₂.2.2.symm)
  all_goals exact roundedResultOf_unique h₁ h₂

theorem convertFromIntSpecOf_unique {fmt : Format} {rm : RoundingDirection} {v : Int}
    (h₁ : ConvertFromIntSpecOf sp fmt rm v r₁) (h₂ : ConvertFromIntSpecOf sp fmt rm v r₂) :
    r₁ = r₂ :=
  roundedResultOf_unique h₁ h₂

end

end SoftFloat.Proof
