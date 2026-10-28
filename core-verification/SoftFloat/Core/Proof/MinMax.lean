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

theorem minMaxLt_iff_valE_lt (fmt : Format) {a b : Nat}
    (hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false) :
    minMaxLt fmt a b ↔ valE fmt a < valE fmt b := by
  unfold minMaxLt
  refine ⟨fun h => h.resolve_right ?_, Or.inl⟩
  rintro ⟨h1, h2⟩
  rw [classify_eq_zero_iff] at h1 h2
  simp [h1.1, h2.1] at hz

theorem minMaxLt_iff_of_isZeroU (fmt : Format) {a b : Nat}
    (ha : isZeroU (fmt.unpack a) = true) (hb : isZeroU (fmt.unpack b) = true) :
    minMaxLt fmt a b ↔ (fmt.unpack a).sign = true ∧ (fmt.unpack b).sign = false := by
  unfold minMaxLt
  rw [valE_of_isZeroU fmt ha, valE_of_isZeroU fmt hb, classify_eq_zero_iff, classify_eq_zero_iff]
  simp [ha, hb]

theorem minMaxLt_sign_of_isZeroU (fmt : Format) {a b : Nat}
    (ha : isZeroU (fmt.unpack a) = true) (hb : isZeroU (fmt.unpack b) = true) :
    (minMaxLt fmt a b → (fmt.unpack a).sign = true) ∧
      (minMaxLt fmt b a → (fmt.unpack a).sign = false) := by
  rw [minMaxLt_iff_of_isZeroU fmt ha hb, minMaxLt_iff_of_isZeroU fmt hb ha]
  exact ⟨fun h => h.1, fun h => h.2⟩

theorem minMaxLt_ltU (fmt : Format) {a b : Nat}
    (ha : isNaN fmt a = false) (hb : isNaN fmt b = false)
    (hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false) :
    (minMaxLt fmt a b → fmt.ltU (fmt.unpack a) (fmt.unpack b) = true) ∧
      (minMaxLt fmt b a → fmt.ltU (fmt.unpack a) (fmt.unpack b) = false) := by
  have hz' : (isZeroU (fmt.unpack b) && isZeroU (fmt.unpack a)) = false := by
    rw [Bool.and_comm]; exact hz
  rw [minMaxLt_iff_valE_lt fmt hz, minMaxLt_iff_valE_lt fmt hz', ← ltU_iff_valE_lt fmt ha hb hz]
  refine ⟨id, fun h => ?_⟩
  cases hl : fmt.ltU (fmt.unpack a) (fmt.unpack b)
  · rfl
  · exact absurd (lt_trans h ((ltU_iff_valE_lt fmt ha hb hz).1 hl)) (lt_irrefl _)

theorem minMaxSelectOf_min (fmt : Format) {a b : Nat} (c : Bool)
    (h1 : minMaxLt fmt a b → c = true) (h2 : minMaxLt fmt b a → c = false) :
    MinMaxSelectOf true fmt a b (if c then a else b) := by
  refine ⟨by cases c <;> simp, fun h => ?_, fun h => ?_⟩
  · simp [h1 h]
  · simp [h2 h]

theorem minMaxSelectOf_max (fmt : Format) {a b : Nat} (c : Bool)
    (h1 : minMaxLt fmt a b → c = true) (h2 : minMaxLt fmt b a → c = false) :
    MinMaxSelectOf false fmt a b (if c then b else a) := by
  refine ⟨by cases c <;> simp, fun h => ?_, fun h => ?_⟩
  · simp [h1 h]
  · simp [h2 h]

theorem ite_lt_two_pow (fmt : Format) {a b : Nat} (c : Bool)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) : (if c then a else b) < 2 ^ fmt.width := by
  cases c <;> simpa

section

variable (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format) {a b : Nat}
  (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
include hsp ha hb

theorem minMaxNumberSpecOf_minimumNumberWith (op : NaNOperation) :
    MinMaxNumberSpecOf sp op true fmt a b (fmt.minimumNumberWith sp op a b) := by
  unfold MinMaxNumberSpecOf Format.minimumNumberWith
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack]
  cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b
  · simp only [Bool.and_self, Bool.false_eq_true, ↓reduceIte]
    cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := minMaxLt_ltU fmt hna hnb hz
      exact ⟨ite_lt_two_pow fmt _ ha hb, minMaxSelectOf_min fmt _ this.1 this.2, trivial⟩
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hz
      have := minMaxLt_sign_of_isZeroU fmt hz.1 hz.2
      exact ⟨ite_lt_two_pow fmt _ ha hb, minMaxSelectOf_min fmt _ this.1 this.2, trivial⟩
  · simp [ha, isSignalingNaN_eq_false_of_isNaN fmt hna]
  · simp [hb, isSignalingNaN_eq_false_of_isNaN fmt hnb]
  · simp only [Bool.and_self, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, by simp, by simp⟩

theorem minMaxNumberSpecOf_maximumNumberWith (op : NaNOperation) :
    MinMaxNumberSpecOf sp op false fmt a b (fmt.maximumNumberWith sp op a b) := by
  unfold MinMaxNumberSpecOf Format.maximumNumberWith
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack]
  cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b
  · simp only [Bool.and_self, Bool.false_eq_true, ↓reduceIte]
    cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := minMaxLt_ltU fmt hna hnb hz
      exact ⟨ite_lt_two_pow fmt _ hb ha, minMaxSelectOf_max fmt _ this.1 this.2, trivial⟩
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hz
      have := minMaxLt_sign_of_isZeroU fmt hz.1 hz.2
      exact ⟨ite_lt_two_pow fmt _ hb ha, minMaxSelectOf_max fmt _ this.1 this.2, trivial⟩
  · simp [ha, isSignalingNaN_eq_false_of_isNaN fmt hna]
  · simp [hb, isSignalingNaN_eq_false_of_isNaN fmt hnb]
  · simp only [Bool.and_self, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, by simp, by simp⟩

theorem minMaxPropagateSpecOf_minimumWith (op : NaNOperation) :
    MinMaxPropagateSpecOf sp op true fmt a b (fmt.minimumWith sp op a b) := by
  unfold MinMaxPropagateSpecOf Format.minimumWith MinMaxNaNOf
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack]
  by_cases hn : (isNaN fmt a || isNaN fmt b) = true
  · simp only [hn, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, by simp, by simp⟩
  · have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := minMaxLt_ltU fmt hna hnb hz
      exact ⟨ite_lt_two_pow fmt _ ha hb, minMaxSelectOf_min fmt _ this.1 this.2, trivial⟩
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hz
      have := minMaxLt_sign_of_isZeroU fmt hz.1 hz.2
      exact ⟨ite_lt_two_pow fmt _ ha hb, minMaxSelectOf_min fmt _ this.1 this.2, trivial⟩

theorem minMaxPropagateSpecOf_maximumWith (op : NaNOperation) :
    MinMaxPropagateSpecOf sp op false fmt a b (fmt.maximumWith sp op a b) := by
  unfold MinMaxPropagateSpecOf Format.maximumWith MinMaxNaNOf
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack, isSNaNU_unpack, isSNaNU_unpack]
  by_cases hn : (isNaN fmt a || isNaN fmt b) = true
  · simp only [hn, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, by simp, by simp⟩
  · have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := minMaxLt_ltU fmt hna hnb hz
      exact ⟨ite_lt_two_pow fmt _ hb ha, minMaxSelectOf_max fmt _ this.1 this.2, trivial⟩
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hz
      have := minMaxLt_sign_of_isZeroU fmt hz.1 hz.2
      exact ⟨ite_lt_two_pow fmt _ hb ha, minMaxSelectOf_max fmt _ this.1 this.2, trivial⟩

theorem minimumNumberSpecOf_minimumNumber :
    MinimumNumberSpecOf sp fmt a b (Format.minimumNumber sp fmt a b) :=
  minMaxNumberSpecOf_minimumNumberWith sp hsp fmt ha hb _

theorem maximumNumberSpecOf_maximumNumber :
    MaximumNumberSpecOf sp fmt a b (Format.maximumNumber sp fmt a b) :=
  minMaxNumberSpecOf_maximumNumberWith sp hsp fmt ha hb _

theorem minimumSpecOf_minimum : MinimumSpecOf sp fmt a b (Format.minimum sp fmt a b) :=
  minMaxPropagateSpecOf_minimumWith sp hsp fmt ha hb _

theorem maximumSpecOf_maximum : MaximumSpecOf sp fmt a b (Format.maximum sp fmt a b) :=
  minMaxPropagateSpecOf_maximumWith sp hsp fmt ha hb _

end

theorem softfloat_minimumNumber (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinimumNumberSpecOf sp fmt a b ((softfloat sp).minimumNumber fmt a b) :=
  fun fmt _ _ ha hb => minimumNumberSpecOf_minimumNumber sp hsp fmt ha hb

theorem softfloat_maximumNumber (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaximumNumberSpecOf sp fmt a b ((softfloat sp).maximumNumber fmt a b) :=
  fun fmt _ _ ha hb => maximumNumberSpecOf_maximumNumber sp hsp fmt ha hb

theorem softfloat_minimum (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinimumSpecOf sp fmt a b ((softfloat sp).minimum fmt a b) :=
  fun fmt _ _ ha hb => minimumSpecOf_minimum sp hsp fmt ha hb

theorem softfloat_maximum (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaximumSpecOf sp fmt a b ((softfloat sp).maximum fmt a b) :=
  fun fmt _ _ ha hb => maximumSpecOf_maximum sp hsp fmt ha hb

section

variable {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}

theorem minMaxLt_total (fmt : Format) {a b : Nat}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false) :
    minMaxLt fmt a b ∨ minMaxLt fmt b a ∨ a = b := by
  rcases lt_trichotomy (valE fmt a) (valE fmt b) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases eq_or_zero_ne_of_valE_eq fmt ha hb hna hnb h with h' | ⟨s, hs, hs'⟩
    · exact Or.inr (Or.inr h')
    · cases s
      · exact Or.inr (Or.inl (Or.inr ⟨hs', hs⟩))
      · exact Or.inl (Or.inr ⟨hs, hs'⟩)
  · exact Or.inr (Or.inl (Or.inl h))

theorem minMaxSelectOf_unique {pickLess : Bool} {fmt : Format} {a b r s : Nat}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false)
    (h₁ : MinMaxSelectOf pickLess fmt a b r) (h₂ : MinMaxSelectOf pickLess fmt a b s) : r = s := by
  rcases minMaxLt_total fmt ha hb hna hnb with h | h | h
  · rw [h₁.2.1 h, h₂.2.1 h]
  · rw [h₁.2.2 h, h₂.2.2 h]
  · subst h
    rcases h₁.1 with h | h <;> rcases h₂.1 with h' | h' <;> rw [h, h']

theorem minMaxNumberSpecOf_unique {op : NaNOperation} {pickLess : Bool} {fmt : Format} {a b : Nat}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinMaxNumberSpecOf sp op pickLess fmt a b r₁)
    (h₂ : MinMaxNumberSpecOf sp op pickLess fmt a b r₂) : r₁ = r₂ := by
  unfold MinMaxNumberSpecOf MinMaxNaNOf at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ with hab hna hnb
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (minMaxSelectOf_unique ha hb (by simpa using hna) (by simpa using hnb) h₁.1 h₂.1)
      (h₁.2.trans h₂.2.symm)

theorem minMaxPropagateSpecOf_unique {op : NaNOperation} {pickLess : Bool} {fmt : Format}
    {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinMaxPropagateSpecOf sp op pickLess fmt a b r₁)
    (h₂ : MinMaxPropagateSpecOf sp op pickLess fmt a b r₂) : r₁ = r₂ := by
  unfold MinMaxPropagateSpecOf MinMaxNaNOf at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ with hn
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    exact Prod.ext (minMaxSelectOf_unique ha hb hn.1 hn.2 h₁.1 h₂.1) (h₁.2.trans h₂.2.symm)

end

end SoftFloat.Proof
