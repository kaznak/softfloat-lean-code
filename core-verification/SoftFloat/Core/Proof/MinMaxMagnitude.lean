/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Order
import SoftFloat.Core.Proof.MinMax

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem magE_withSign (fmt : Format) (n : Nat) (s : Bool) :
    magE fmt (withSign fmt n s) = magE fmt n := by
  unfold magE; rw [unpack_withSign]; rfl

theorem isNaN_withSign (fmt : Format) (n : Nat) (s : Bool) :
    isNaN fmt (withSign fmt n s) = isNaN fmt n := by
  unfold isNaN; rw [classify_withSign]; cases classify fmt n <;> rfl

theorem valE_withSign_false (fmt : Format) {n : Nat} (h : isNaN fmt n = false) :
    valE fmt (withSign fmt n false) = magE fmt n := by
  rw [valE_eq_magE fmt ((isNaN_withSign fmt n false).trans h), unpack_withSign, magE_withSign]
  rfl

theorem magnitudeLt_iff (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) :
    magnitudeLt fmt a b ↔ fmt.orderKeyU (fmt.unpack a) < fmt.orderKeyU (fmt.unpack b) := by
  unfold magnitudeLt
  rw [valE_withSign_false fmt ha, valE_withSign_false fmt hb, orderKeyU_lt_iff_magE_lt fmt ha hb]
  simp [ha, hb]

theorem not_magnitudeLt_of_isNaN (fmt : Format) {a b : Nat}
    (h : (isNaN fmt a || isNaN fmt b) = true) :
    ¬ magnitudeLt fmt a b ∧ ¬ magnitudeLt fmt b a := by
  refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> simp [h'.1, h'.2.1] at h

theorem magnitudeSelectOf_magnitudeSelect (fmt : Format) (pickLess : Bool) {a b : Nat}
    {P : Nat × StatusFlags → Prop} {r : Nat × StatusFlags} (h : P r) :
    MagnitudeSelectOf pickLess fmt a b P (fmt.magnitudeSelect pickLess a b r) := by
  unfold MagnitudeSelectOf Format.magnitudeSelect
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack]
  by_cases hn : (isNaN fmt a || isNaN fmt b) = true
  · have h' := not_magnitudeLt_of_isNaN fmt hn
    simp only [hn, ↓reduceIte]
    exact ⟨fun h1 => absurd h1 h'.1, fun h1 => absurd h1 h'.2, fun _ _ => h⟩
  · have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rw [magnitudeLt_iff fmt hna hnb, magnitudeLt_iff fmt hnb hna]
    by_cases hlt : fmt.orderKeyU (fmt.unpack a) < fmt.orderKeyU (fmt.unpack b)
    · simp [hlt, not_lt_of_gt hlt]
    · by_cases hgt : fmt.orderKeyU (fmt.unpack b) < fmt.orderKeyU (fmt.unpack a)
      · simp [hlt, hgt]
      · simp [hlt, hgt, h]

section

variable (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format) {a b : Nat}
  (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
include hsp ha hb

theorem minimumMagnitudeSpecOf_minimumMagnitude :
    MinimumMagnitudeSpecOf sp fmt a b (Format.minimumMagnitude sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt true (minMaxPropagateSpecOf_minimumWith sp hsp fmt ha hb _)

theorem minimumMagnitudeNumberSpecOf_minimumMagnitudeNumber :
    MinimumMagnitudeNumberSpecOf sp fmt a b (Format.minimumMagnitudeNumber sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt true
    (minMaxNumberSpecOf_minimumNumberWith sp hsp fmt ha hb _)

theorem maximumMagnitudeSpecOf_maximumMagnitude :
    MaximumMagnitudeSpecOf sp fmt a b (Format.maximumMagnitude sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt false (minMaxPropagateSpecOf_maximumWith sp hsp fmt ha hb _)

theorem maximumMagnitudeNumberSpecOf_maximumMagnitudeNumber :
    MaximumMagnitudeNumberSpecOf sp fmt a b (Format.maximumMagnitudeNumber sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt false
    (minMaxNumberSpecOf_maximumNumberWith sp hsp fmt ha hb _)

end

theorem softfloat_minimumMagnitude_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinimumMagnitudeSpecOf sp fmt a b ((softfloat sp).minimumMagnitude fmt a b) :=
  fun fmt _ _ ha hb => minimumMagnitudeSpecOf_minimumMagnitude sp hsp fmt ha hb

theorem softfloat_minimumMagnitudeNumber_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinimumMagnitudeNumberSpecOf sp fmt a b ((softfloat sp).minimumMagnitudeNumber fmt a b) :=
  fun fmt _ _ ha hb => minimumMagnitudeNumberSpecOf_minimumMagnitudeNumber sp hsp fmt ha hb

theorem softfloat_maximumMagnitude_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaximumMagnitudeSpecOf sp fmt a b ((softfloat sp).maximumMagnitude fmt a b) :=
  fun fmt _ _ ha hb => maximumMagnitudeSpecOf_maximumMagnitude sp hsp fmt ha hb

theorem softfloat_maximumMagnitudeNumber_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaximumMagnitudeNumberSpecOf sp fmt a b ((softfloat sp).maximumMagnitudeNumber fmt a b) :=
  fun fmt _ _ ha hb => maximumMagnitudeNumberSpecOf_maximumMagnitudeNumber sp hsp fmt ha hb

section

variable {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}

theorem magnitudeSelectOf_unique {pickLess : Bool} {fmt : Format} {a b : Nat}
    {P : Nat × StatusFlags → Prop} (hP : ∀ {s₁ s₂}, P s₁ → P s₂ → s₁ = s₂)
    (h₁ : MagnitudeSelectOf pickLess fmt a b P r₁) (h₂ : MagnitudeSelectOf pickLess fmt a b P r₂) :
    r₁ = r₂ := by
  by_cases hab : magnitudeLt fmt a b
  · rw [h₁.1 hab, h₂.1 hab]
  · by_cases hba : magnitudeLt fmt b a
    · rw [h₁.2.1 hba, h₂.2.1 hba]
    · exact hP (h₁.2.2 hab hba) (h₂.2.2 hab hba)

theorem minimumMagnitudeSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinimumMagnitudeSpecOf sp fmt a b r₁) (h₂ : MinimumMagnitudeSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minMaxPropagateSpecOf_unique ha hb) h₁ h₂

theorem minimumMagnitudeNumberSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinimumMagnitudeNumberSpecOf sp fmt a b r₁) (h₂ : MinimumMagnitudeNumberSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minMaxNumberSpecOf_unique ha hb) h₁ h₂

theorem maximumMagnitudeSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MaximumMagnitudeSpecOf sp fmt a b r₁) (h₂ : MaximumMagnitudeSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minMaxPropagateSpecOf_unique ha hb) h₁ h₂

theorem maximumMagnitudeNumberSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MaximumMagnitudeNumberSpecOf sp fmt a b r₁) (h₂ : MaximumMagnitudeNumberSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minMaxNumberSpecOf_unique ha hb) h₁ h₂

end

end SoftFloat.Proof
