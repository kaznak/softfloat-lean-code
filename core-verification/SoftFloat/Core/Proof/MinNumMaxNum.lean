/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.MinMax
import SoftFloat.Core.Proof.MinMaxMagnitude
import SoftFloat.Core.Proof.TotalOrder

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem ltU_eq_false_of_isZeroU (fmt : Format) {u v : Unpacked} (hu : isZeroU u = true)
    (hv : isZeroU v = true) : fmt.ltU u v = false := by
  unfold Format.isZeroU at hu hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hu hv
  unfold Format.ltU Format.orderKeyU Format.isZeroU
  simp [hu, hv]

theorem valE_ne_of_ltU (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false) (hb : isNaN fmt b = false)
    (h : (fmt.ltU (fmt.unpack a) (fmt.unpack b) || fmt.ltU (fmt.unpack b) (fmt.unpack a)) = true) :
    valE fmt a < valE fmt b ∨ valE fmt b < valE fmt a := by
  by_cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = true
  · simp only [Bool.and_eq_true] at hz
    rw [ltU_eq_false_of_isZeroU fmt hz.1 hz.2, ltU_eq_false_of_isZeroU fmt hz.2 hz.1] at h
    simp at h
  · have hz' : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false := by simpa using hz
    have hz'' : (isZeroU (fmt.unpack b) && isZeroU (fmt.unpack a)) = false := by
      rw [Bool.and_comm]; exact hz'
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact Or.inl ((ltU_iff_valE_lt fmt ha hb hz').1 h)
    · exact Or.inr ((ltU_iff_valE_lt fmt hb ha hz'').1 h)

theorem valE_eq_of_not_ltU (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false) (hb : isNaN fmt b = false)
    (h : (fmt.ltU (fmt.unpack a) (fmt.unpack b) || fmt.ltU (fmt.unpack b) (fmt.unpack a)) = false) :
    valE fmt a = valE fmt b := by
  rcases lt_trichotomy (valE fmt a) (valE fmt b) with h1 | h1 | h1
  · have := (ltU_iff_valE_lt fmt ha hb (not_both_zero_of_valE_lt fmt h1)).2 h1
    simp [this] at h
  · exact h1
  · have := (ltU_iff_valE_lt fmt hb ha (not_both_zero_of_valE_lt fmt h1)).2 h1
    simp [this] at h

theorem minNumMaxNumSelectOf_of_minMaxSelectOf {sp : Specialization} {eq : MinNumMaxNumOperation}
    {pickLess : Bool} {fmt : Format} {a b r : Nat} (hs : MinMaxSelectOf pickLess fmt a b r)
    (hne : valE fmt a < valE fmt b ∨ valE fmt b < valE fmt a) : MinNumMaxNumSelectOf sp eq pickLess fmt a b r :=
  ⟨fun h => hs.2.1 (Or.inl h), fun h => hs.2.2 (Or.inl h),
    fun h => by rcases hne with h' | h' <;> rw [h] at h' <;> exact absurd h' (lt_irrefl _)⟩

theorem minNumMaxNumOfEqual_lt {sp : Specialization} (hsp : Specialization.Valid sp)
    (eq : MinNumMaxNumOperation) (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) :
    sp.minNumMaxNumOfEqual eq fmt a b < 2 ^ fmt.width := by
  rcases hsp.minNumMaxNumOfEqual eq fmt a b with h | h <;> rw [h] <;> assumption

section

variable (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format) {a b : Nat}
  (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
include hsp ha hb

theorem minNumMaxNumSpecOf_minNumWith (op : NaNOperation) (eq : MinNumMaxNumOperation) :
    MinNumMaxNumSpecOf sp op eq true fmt a b (fmt.minNumWith sp op eq a b) := by
  have hm := minMaxNumberSpecOf_minimumNumberWith sp hsp fmt ha hb op
  unfold MinNumMaxNumSpecOf Format.minNumWith Format.signalingNaNResult
  dsimp only
  rw [isSNaNU_unpack, isSNaNU_unpack, isNaNU_unpack, isNaNU_unpack]
  by_cases hs : (isSignalingNaN fmt a || isSignalingNaN fmt b) = true
  · simp only [hs, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b
    · unfold MinMaxNumberSpecOf at hm
      simp only [hna, hnb, Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      cases hl : (fmt.ltU (fmt.unpack a) (fmt.unpack b) || fmt.ltU (fmt.unpack b) (fmt.unpack a))
      · have he := valE_eq_of_not_ltU fmt hna hnb hl
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨minNumMaxNumOfEqual_lt hsp eq fmt ha hb,
          ⟨fun h => absurd (he ▸ h) (lt_irrefl _), fun h => absurd (he ▸ h) (lt_irrefl _), fun _ => rfl⟩, trivial⟩
      · simp only [↓reduceIte]
        exact ⟨hm.1, minNumMaxNumSelectOf_of_minMaxSelectOf hm.2.1 (valE_ne_of_ltU fmt hna hnb hl), hm.2.2⟩
    all_goals simpa using hm

theorem minNumMaxNumSpecOf_maxNumWith (op : NaNOperation) (eq : MinNumMaxNumOperation) :
    MinNumMaxNumSpecOf sp op eq false fmt a b (fmt.maxNumWith sp op eq a b) := by
  have hm := minMaxNumberSpecOf_maximumNumberWith sp hsp fmt ha hb op
  unfold MinNumMaxNumSpecOf Format.maxNumWith Format.signalingNaNResult
  dsimp only
  rw [isSNaNU_unpack, isSNaNU_unpack, isNaNU_unpack, isNaNU_unpack]
  by_cases hs : (isSignalingNaN fmt a || isSignalingNaN fmt b) = true
  · simp only [hs, ↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩
  · simp only [hs, Bool.false_eq_true, ↓reduceIte]
    cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b
    · unfold MinMaxNumberSpecOf at hm
      simp only [hna, hnb, Bool.and_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      cases hl : (fmt.ltU (fmt.unpack a) (fmt.unpack b) || fmt.ltU (fmt.unpack b) (fmt.unpack a))
      · have he := valE_eq_of_not_ltU fmt hna hnb hl
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨minNumMaxNumOfEqual_lt hsp eq fmt ha hb,
          ⟨fun h => absurd (he ▸ h) (lt_irrefl _), fun h => absurd (he ▸ h) (lt_irrefl _), fun _ => rfl⟩, trivial⟩
      · simp only [↓reduceIte]
        exact ⟨hm.1, minNumMaxNumSelectOf_of_minMaxSelectOf hm.2.1 (valE_ne_of_ltU fmt hna hnb hl), hm.2.2⟩
    all_goals simpa using hm

theorem minNumSpecOf_minNum : MinNumSpecOf sp fmt a b (Format.minNum sp fmt a b) :=
  minNumMaxNumSpecOf_minNumWith sp hsp fmt ha hb _ _

theorem maxNumSpecOf_maxNum : MaxNumSpecOf sp fmt a b (Format.maxNum sp fmt a b) :=
  minNumMaxNumSpecOf_maxNumWith sp hsp fmt ha hb _ _

theorem minNumMagSpecOf_minNumMag : MinNumMagSpecOf sp fmt a b (Format.minNumMag sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt true (minNumMaxNumSpecOf_minNumWith sp hsp fmt ha hb _ _)

theorem maxNumMagSpecOf_maxNumMag : MaxNumMagSpecOf sp fmt a b (Format.maxNumMag sp fmt a b) :=
  magnitudeSelectOf_magnitudeSelect fmt false (minNumMaxNumSpecOf_maxNumWith sp hsp fmt ha hb _ _)

end

theorem softfloat_minNum_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinNumSpecOf sp fmt a b ((softfloat sp).minNum fmt a b) :=
  fun fmt _ _ ha hb => minNumSpecOf_minNum sp hsp fmt ha hb

theorem softfloat_maxNum_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaxNumSpecOf sp fmt a b ((softfloat sp).maxNum fmt a b) :=
  fun fmt _ _ ha hb => maxNumSpecOf_maxNum sp hsp fmt ha hb

theorem softfloat_minNumMag_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MinNumMagSpecOf sp fmt a b ((softfloat sp).minNumMag fmt a b) :=
  fun fmt _ _ ha hb => minNumMagSpecOf_minNumMag sp hsp fmt ha hb

theorem softfloat_maxNumMag_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      MaxNumMagSpecOf sp fmt a b ((softfloat sp).maxNumMag fmt a b) :=
  fun fmt _ _ ha hb => maxNumMagSpecOf_maxNumMag sp hsp fmt ha hb

section

variable {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}

theorem minNumMaxNumSpecOf_unique {op : NaNOperation} {eq : MinNumMaxNumOperation} {pickLess : Bool}
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinNumMaxNumSpecOf sp op eq pickLess fmt a b r₁)
    (h₂ : MinNumMaxNumSpecOf sp op eq pickLess fmt a b r₂) : r₁ = r₂ := by
  unfold MinNumMaxNumSpecOf at h₁ h₂
  split_ifs at h₁ h₂
  · exact Prod.ext (h₁.2.1.trans h₂.2.1.symm) (h₁.2.2.trans h₂.2.2.symm)
  · exact minMaxNumberSpecOf_unique ha hb h₁ h₂
  · obtain ⟨-, s₁, f₁⟩ := h₁
    obtain ⟨-, s₂, f₂⟩ := h₂
    refine Prod.ext ?_ (f₁.trans f₂.symm)
    rcases lt_trichotomy (valE fmt a) (valE fmt b) with h | h | h
    · exact (s₁.1 h).trans (s₂.1 h).symm
    · exact (s₁.2.2 h).trans (s₂.2.2 h).symm
    · exact (s₁.2.1 h).trans (s₂.2.1 h).symm

theorem minNumSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinNumSpecOf sp fmt a b r₁) (h₂ : MinNumSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  minNumMaxNumSpecOf_unique ha hb h₁ h₂

theorem maxNumSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MaxNumSpecOf sp fmt a b r₁) (h₂ : MaxNumSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  minNumMaxNumSpecOf_unique ha hb h₁ h₂

theorem minNumMagSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MinNumMagSpecOf sp fmt a b r₁) (h₂ : MinNumMagSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minNumMaxNumSpecOf_unique ha hb) h₁ h₂

theorem maxNumMagSpecOf_unique {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h₁ : MaxNumMagSpecOf sp fmt a b r₁) (h₂ : MaxNumMagSpecOf sp fmt a b r₂) : r₁ = r₂ :=
  magnitudeSelectOf_unique (minNumMaxNumSpecOf_unique ha hb) h₁ h₂

end

end SoftFloat.Proof
