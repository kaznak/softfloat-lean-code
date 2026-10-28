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

theorem two_pow_width_sub_one_eq (fmt : Format) :
    2 ^ (fmt.width - 1) = (fmt.expMax + 1) * 2 ^ fmt.fracBits := by
  rw [width_sub_one, pow_add, expMax_add_one]

theorem two_pow_width_eq (fmt : Format) : 2 ^ fmt.width = 2 * 2 ^ (fmt.width - 1) := by
  rw [width_eq fmt, Nat.add_sub_cancel, pow_succ]; ring

theorem orderKeyU_unpack (fmt : Format) (n : Nat) :
    fmt.orderKeyU (fmt.unpack n) = n % 2 ^ (fmt.width - 1) := by
  unfold Format.orderKeyU Format.unpack
  dsimp only
  rw [width_sub_one, Nat.add_comm fmt.expBits, pow_add, Nat.mod_mul]
  ring

theorem unpack_add_two_pow (fmt : Format) (s : Bool) {k : Nat} (hk : k < 2 ^ (fmt.width - 1)) :
    (fmt.unpack ((if s then 2 ^ (fmt.width - 1) else 0) + k)).sign = s ∧
      fmt.orderKeyU (fmt.unpack ((if s then 2 ^ (fmt.width - 1) else 0) + k)) = k := by
  have hW : 0 < 2 ^ (fmt.width - 1) := by positivity
  rw [unpack_sign_eq, orderKeyU_unpack]
  cases s
  · simp [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
  · have h1 : (2 ^ (fmt.width - 1) + k) / 2 ^ (fmt.width - 1) = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hW, Nat.div_eq_of_lt hk]
    have h2 : (2 ^ (fmt.width - 1) + k) % 2 ^ (fmt.width - 1) = k := by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
    simp [h1, h2]

theorem eq_add_orderKeyU (fmt : Format) {n : Nat} (hn : n < 2 ^ fmt.width) :
    n = (if (fmt.unpack n).sign then 2 ^ (fmt.width - 1) else 0) + fmt.orderKeyU (fmt.unpack n) := by
  conv_lhs => rw [← pack_unpack fmt hn]
  rw [pack_eq_add]
  unfold Format.pack Format.orderKeyU
  simp

theorem orderKeyU_lt (fmt : Format) (n : Nat) :
    fmt.orderKeyU (fmt.unpack n) < 2 ^ (fmt.width - 1) := by
  rw [orderKeyU_unpack]; exact Nat.mod_lt _ (by positivity)

theorem isZeroU_iff_orderKeyU_eq_zero (fmt : Format) (u : Unpacked) :
    isZeroU u = true ↔ fmt.orderKeyU u = 0 := by
  have hM : 0 < 2 ^ fmt.fracBits := by positivity
  unfold Format.isZeroU Format.orderKeyU
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
  · rintro ⟨h1 | h1, h2⟩
    · exact ⟨h1, h2⟩
    · omega

theorem isNaN_iff_orderKeyU_gt (fmt : Format) (n : Nat) :
    isNaN fmt n = true ↔ fmt.expMax * 2 ^ fmt.fracBits < fmt.orderKeyU (fmt.unpack n) := by
  rw [← isNaNU_unpack]
  have he := unpack_expField_lt fmt n
  have hm := expMax_add_one fmt
  unfold Format.isNaNU
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases hE : (fmt.unpack n).expField = fmt.expMax
  · unfold Format.orderKeyU; rw [hE]; omega
  · have := orderKeyU_lt_of_expField_lt fmt (u := fmt.unpack n) (by omega)
      (unpack_fracField_lt fmt n)
    simp only [hE, false_and, false_iff, not_lt]; omega

theorem isInfU_iff_orderKeyU_eq (fmt : Format) (n : Nat) :
    fmt.isInfU (fmt.unpack n) = true ↔
      fmt.orderKeyU (fmt.unpack n) = fmt.expMax * 2 ^ fmt.fracBits := by
  have he := unpack_expField_lt fmt n
  have hm := expMax_add_one fmt
  unfold Format.isInfU
  simp only [Bool.and_eq_true, beq_iff_eq]
  by_cases hE : (fmt.unpack n).expField = fmt.expMax
  · unfold Format.orderKeyU; rw [hE]; omega
  · have := orderKeyU_lt_of_expField_lt fmt (u := fmt.unpack n) (by omega)
      (unpack_fracField_lt fmt n)
    simp only [hE, false_and, false_iff]; omega

def signedKey (fmt : Format) (n : Nat) : Int :=
  if (fmt.unpack n).sign then -(fmt.orderKeyU (fmt.unpack n) : Int)
  else (fmt.orderKeyU (fmt.unpack n) : Int)

theorem valE_lt_iff_signedKey_lt (fmt : Format) {a b : Nat}
    (ha : isNaN fmt a = false) (hb : isNaN fmt b = false) :
    valE fmt a < valE fmt b ↔ signedKey fmt a < signedKey fmt b := by
  have za := isZeroU_iff_orderKeyU_eq_zero fmt (fmt.unpack a)
  have zb := isZeroU_iff_orderKeyU_eq_zero fmt (fmt.unpack b)
  unfold signedKey
  cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b))
  · rw [← ltU_iff_valE_lt fmt ha hb hz]
    have hz' : ¬ (fmt.orderKeyU (fmt.unpack a) = 0 ∧ fmt.orderKeyU (fmt.unpack b) = 0) := by
      rw [← za, ← zb]; simpa using hz
    unfold Format.ltU
    rw [hz]
    cases hsa : (fmt.unpack a).sign <;> cases hsb : (fmt.unpack b).sign <;> simp
    all_goals omega
  · simp only [Bool.and_eq_true] at hz
    rw [valE_of_isZeroU fmt hz.1, valE_of_isZeroU fmt hz.2, za.1 hz.1, zb.1 hz.2]
    simp

theorem valE_eq_zero_iff (fmt : Format) {n : Nat} (hn : isNaN fmt n = false) :
    valE fmt n = 0 ↔ isZeroU (fmt.unpack n) = true := by
  constructor
  · intro h
    by_contra hz
    have hp := magE_pos fmt (by simpa using hz)
    rw [valE_eq_magE fmt hn] at h
    split_ifs at h
    · rw [EReal.neg_eq_zero_iff] at h; rw [h] at hp; exact lt_irrefl _ hp
    · rw [h] at hp; exact lt_irrefl _ hp
  · exact valE_of_isZeroU fmt

theorem isLeastGreater_of_signedKey (fmt : Format) {x r : Nat} (hx : isNaN fmt x = false)
    (hr : isNaN fmt r = false) (h : signedKey fmt r = signedKey fmt x + 1) :
    IsLeastGreater fmt x r := by
  refine ⟨hr, (valE_lt_iff_signedKey_lt fmt hx hr).2 (by omega), fun y _ hy hxy => ?_⟩
  have h1 := (valE_lt_iff_signedKey_lt fmt hx hy).1 hxy
  exact not_lt.1 fun h2 => absurd ((valE_lt_iff_signedKey_lt fmt hy hr).1 h2) (by omega)

theorem classify_zero_true_of_valE_eq_zero (fmt : Format) {r : Nat} (hr : isNaN fmt r = false)
    (hs : (fmt.unpack r).sign = true) : valE fmt r = 0 → classify fmt r = .zero true := fun h =>
  (classify_eq_zero_iff fmt r true).2 ⟨(valE_eq_zero_iff fmt hr).1 h, hs⟩

theorem signedKey_eq_zero_of_isZeroU (fmt : Format) {x : Nat} (hz : isZeroU (fmt.unpack x) = true) :
    signedKey fmt x = 0 := by
  unfold signedKey; rw [(isZeroU_iff_orderKeyU_eq_zero fmt _).1 hz]; simp

theorem nextUp_zero_case (fmt : Format) {x : Nat} (hn : isNaN fmt x = false)
    (hz : isZeroU (fmt.unpack x) = true) :
    fmt.pack false 0 1 < 2 ^ fmt.width ∧ IsLeastGreater fmt x (fmt.pack false 0 1)
      ∧ (valE fmt (fmt.pack false 0 1) = 0 → classify fmt (fmt.pack false 0 1) = .zero true) := by
  have h1 : 1 < 2 ^ fmt.fracBits := Nat.one_lt_two_pow (by have := one_le_fracBits fmt; omega)
  have h0 : 0 < 2 ^ fmt.expBits := by positivity
  have hu := unpack_pack fmt false h0 h1
  have hkey : fmt.orderKeyU (fmt.unpack (fmt.pack false 0 1)) = 1 := by
    rw [hu]; simp [Format.orderKeyU]
  have hE : 1 ≤ fmt.expMax := Nat.one_le_iff_ne_zero.2 (expMax_ne_zero fmt)
  have hP : 1 ≤ fmt.expMax * 2 ^ fmt.fracBits := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (expMax_ne_zero fmt) (by positivity))
  have hrn : isNaN fmt (fmt.pack false 0 1) = false := by
    cases h : isNaN fmt (fmt.pack false 0 1)
    · rfl
    · have := (isNaN_iff_orderKeyU_gt fmt _).1 h; omega
  refine ⟨pack_lt fmt false h0 h1, isLeastGreater_of_signedKey fmt hn hrn ?_, fun h => ?_⟩
  · rw [signedKey_eq_zero_of_isZeroU fmt hz]
    unfold signedKey; rw [hkey, hu]; simp
  · have := (isZeroU_iff_orderKeyU_eq_zero fmt _).1 ((valE_eq_zero_iff fmt hrn).1 h); omega

theorem nextUp_neg_case (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) (hn : isNaN fmt x = false)
    (hz : isZeroU (fmt.unpack x) = false) (hs : (fmt.unpack x).sign = true) :
    x - 1 < 2 ^ fmt.width ∧ IsLeastGreater fmt x (x - 1)
      ∧ (valE fmt (x - 1) = 0 → classify fmt (x - 1) = .zero true) := by
  have hxe := eq_add_orderKeyU fmt hx
  have hk := orderKeyU_lt fmt x
  have hk0 : fmt.orderKeyU (fmt.unpack x) ≠ 0 := fun h => by
    rw [← isZeroU_iff_orderKeyU_eq_zero] at h; rw [h] at hz; exact absurd hz (by simp)
  have hkn := (isNaN_iff_orderKeyU_gt fmt x).not.1 (by simp [hn])
  rw [hs] at hxe
  simp only [↓reduceIte] at hxe
  have hr : x - 1 = (if true then 2 ^ (fmt.width - 1) else 0) + (fmt.orderKeyU (fmt.unpack x) - 1) := by
    simp only [↓reduceIte]; omega
  obtain ⟨hrs, hrk⟩ := unpack_add_two_pow fmt true (k := fmt.orderKeyU (fmt.unpack x) - 1) (by omega)
  rw [← hr] at hrs hrk
  have hrn : isNaN fmt (x - 1) = false := by
    cases h : isNaN fmt (x - 1)
    · rfl
    · have := (isNaN_iff_orderKeyU_gt fmt _).1 h; omega
  refine ⟨by omega, isLeastGreater_of_signedKey fmt hn hrn ?_,
    classify_zero_true_of_valE_eq_zero fmt hrn hrs⟩
  unfold signedKey; rw [hrs, hrk, hs]; simp only [↓reduceIte]; omega

theorem nextUp_pos_case (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) (hn : isNaN fmt x = false)
    (hs : (fmt.unpack x).sign = false) (hi : fmt.isInfU (fmt.unpack x) = false) :
    x + 1 < 2 ^ fmt.width ∧ IsLeastGreater fmt x (x + 1)
      ∧ (valE fmt (x + 1) = 0 → classify fmt (x + 1) = .zero true) := by
  have hW := two_pow_width_sub_one_eq fmt
  have hW2 := two_pow_width_eq fmt
  have hxe := eq_add_orderKeyU fmt hx
  have hkn := (isNaN_iff_orderKeyU_gt fmt x).not.1 (by simp [hn])
  have hki := (isInfU_iff_orderKeyU_eq fmt x).not.1 (by simp [hi])
  have hM : 2 ^ (fmt.width - 1) = fmt.expMax * 2 ^ fmt.fracBits + 2 ^ fmt.fracBits := by
    rw [hW]; ring
  have hM0 : 0 < 2 ^ fmt.fracBits := by positivity
  rw [hs] at hxe
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hxe
  have hr : x + 1 = (if false then 2 ^ (fmt.width - 1) else 0) + (fmt.orderKeyU (fmt.unpack x) + 1) := by
    simp only [Bool.false_eq_true, ↓reduceIte]; omega
  obtain ⟨hrs, hrk⟩ := unpack_add_two_pow fmt false (k := fmt.orderKeyU (fmt.unpack x) + 1) (by omega)
  rw [← hr] at hrs hrk
  have hrn : isNaN fmt (x + 1) = false := by
    cases h : isNaN fmt (x + 1)
    · rfl
    · have := (isNaN_iff_orderKeyU_gt fmt _).1 h; omega
  refine ⟨by omega, isLeastGreater_of_signedKey fmt hn hrn ?_, fun h => ?_⟩
  · unfold signedKey; rw [hrs, hrk, hs]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · have := (isZeroU_iff_orderKeyU_eq_zero fmt _).1 ((valE_eq_zero_iff fmt hrn).1 h); omega

theorem withSign_withSign (fmt : Format) (x : Nat) (s t : Bool) :
    withSign fmt (withSign fmt x s) t = withSign fmt x t := by
  rw [withSign_eq, unpack_withSign]; rfl

theorem withSign_not_sign_withSign_not_sign (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    withSign fmt (withSign fmt x (!(fmt.unpack x).sign))
      (!(fmt.unpack (withSign fmt x (!(fmt.unpack x).sign))).sign) = x := by
  rw [withSign_withSign, unpack_withSign]
  simp only [Bool.not_not]
  exact withSign_self fmt hx

section

variable {sp : Specialization} (hsp : Specialization.Valid sp) {fmt : Format} {x : Nat}
  (hx : x < 2 ^ fmt.width)
include hsp hx

theorem nextUpSpecOf_nextUp : NextUpSpecOf sp fmt x (Format.nextUp sp fmt x) := by
  unfold NextUpSpecOf Format.nextUp nextNaNResultOf
  dsimp only
  rw [isNaNU_unpack, isSNaNU_unpack]
  cases hn : isNaN fmt x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hinf : (fmt.isInfU (fmt.unpack x) && !(fmt.unpack x).sign) = true
    · have hc : classify fmt x = .infinity false := by
        rw [classify_eq_infinity_iff]; simpa using hinf
      simp only [hinf, ↓reduceIte, hc]
      exact ⟨hx, trivial, trivial⟩
    · have hc : classify fmt x ≠ .infinity false := by
        rw [Ne, classify_eq_infinity_iff]; simpa using hinf
      simp only [hinf, hc, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hz hs
      · obtain ⟨h1, h2, h3⟩ := nextUp_zero_case fmt hn hz
        exact ⟨h1, rfl, h2, h3⟩
      · obtain ⟨h1, h2, h3⟩ := nextUp_neg_case fmt hx hn (by simpa using hz) hs
        exact ⟨h1, rfl, h2, h3⟩
      · have hi : fmt.isInfU (fmt.unpack x) = false := by simp_all
        obtain ⟨h1, h2, h3⟩ := nextUp_pos_case fmt hx hn (by simpa using hs) hi
        exact ⟨h1, rfl, h2, h3⟩
  · simp only [↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩

theorem nextDownSpecOf_nextDown : NextDownSpecOf sp fmt x (Format.nextDown sp fmt x) := by
  unfold NextDownSpecOf Format.nextDown nextNaNResultOf
  dsimp only
  rw [isNaNU_unpack, isSNaNU_unpack]
  cases hn : isNaN fmt x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnx : fmt.negate x = withSign fmt x (!(fmt.unpack x).sign) := flipSign_eq_withSign fmt hx
    have hu := nextUpSpecOf_nextUp hsp (withSign_lt fmt x (!(fmt.unpack x).sign))
    have hy := hu.1
    have hneg : fmt.negate (Format.nextUp sp fmt (fmt.negate x)).1
        = withSign fmt (Format.nextUp sp fmt (fmt.negate x)).1
          (!(fmt.unpack (Format.nextUp sp fmt (fmt.negate x)).1).sign) := by
      rw [hnx]; exact flipSign_eq_withSign fmt hy
    rw [hneg, withSign_not_sign_withSign_not_sign fmt (by rw [hnx]; exact hy), hnx]
    exact ⟨withSign_lt _ _ _, hu⟩
  · simp only [↓reduceIte]
    exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩

end

theorem softfloat_nextUp_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt x, x < 2 ^ fmt.width → NextUpSpecOf sp fmt x ((softfloat sp).nextUp fmt x) :=
  fun _ _ hx => nextUpSpecOf_nextUp hsp hx

theorem softfloat_nextDown_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt x, x < 2 ^ fmt.width → NextDownSpecOf sp fmt x ((softfloat sp).nextDown fmt x) :=
  fun _ _ hx => nextDownSpecOf_nextDown hsp hx

theorem signedKey_eq_of_valE_eq (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) (h : valE fmt a = valE fmt b) : signedKey fmt a = signedKey fmt b := by
  have h1 := (valE_lt_iff_signedKey_lt fmt ha hb).not.1 (by rw [h]; exact lt_irrefl _)
  have h2 := (valE_lt_iff_signedKey_lt fmt hb ha).not.1 (by rw [h]; exact lt_irrefl _)
  omega

theorem nextUpSpecOf_unique {sp : Specialization} {fmt : Format} {x : Nat}
    {r₁ r₂ : Nat × StatusFlags} (h₁ : NextUpSpecOf sp fmt x r₁) (h₂ : NextUpSpecOf sp fmt x r₂) :
    r₁ = r₂ := by
  unfold NextUpSpecOf nextNaNResultOf at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ with hn hc
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · obtain ⟨hi₁, hs₁⟩ := (classify_eq_infinity_iff fmt _ false).1 h₁.2
    obtain ⟨hi₂, hs₂⟩ := (classify_eq_infinity_iff fmt _ false).1 h₂.2
    refine Prod.ext (eq_of_sign_eq_of_orderKeyU_eq fmt hw₁ hw₂ (hs₁.trans hs₂.symm) ?_)
      (h₁.1.trans h₂.1.symm)
    rw [(isInfU_iff_orderKeyU_eq fmt _).1 hi₁, (isInfU_iff_orderKeyU_eq fmt _).1 hi₂]
  · obtain ⟨hf₁, ⟨hn₁, _, hl₁⟩, hz₁⟩ := h₁
    obtain ⟨hf₂, ⟨hn₂, _, hl₂⟩, hz₂⟩ := h₂
    have he : valE fmt r₁.1 = valE fmt r₂.1 :=
      le_antisymm (hl₁ _ hw₂ hn₂ (by assumption)) (hl₂ _ hw₁ hn₁ (by assumption))
    have hk := signedKey_eq_of_valE_eq fmt hn₁ hn₂ he
    have hs : (fmt.unpack r₁.1).sign = (fmt.unpack r₂.1).sign := by
      by_cases h0 : valE fmt r₁.1 = 0
      · rw [((classify_eq_zero_iff fmt _ true).1 (hz₁ h0)).2,
          ((classify_eq_zero_iff fmt _ true).1 (hz₂ (he ▸ h0))).2]
      · have hk0 : fmt.orderKeyU (fmt.unpack r₁.1) ≠ 0 := fun h => h0 ((valE_eq_zero_iff fmt hn₁).2
          ((isZeroU_iff_orderKeyU_eq_zero fmt _).2 h))
        unfold signedKey at hk
        cases hs₁ : (fmt.unpack r₁.1).sign <;> cases hs₂ : (fmt.unpack r₂.1).sign <;>
          simp only [hs₁, hs₂, Bool.false_eq_true, ↓reduceIte] at hk <;> first | rfl | omega
    refine Prod.ext (eq_of_sign_eq_of_orderKeyU_eq fmt hw₁ hw₂ hs ?_) (hf₁.trans hf₂.symm)
    unfold signedKey at hk
    rw [hs] at hk
    cases h : (fmt.unpack r₂.1).sign <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at hk <;> omega

theorem nextDownSpecOf_unique {sp : Specialization} {fmt : Format} {x : Nat}
    {r₁ r₂ : Nat × StatusFlags} (h₁ : NextDownSpecOf sp fmt x r₁)
    (h₂ : NextDownSpecOf sp fmt x r₂) : r₁ = r₂ := by
  unfold NextDownSpecOf nextNaNResultOf at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ with hn
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · have h := nextUpSpecOf_unique h₁ h₂
    simp only [Prod.mk.injEq] at h
    refine Prod.ext ?_ h.2
    rw [← withSign_not_sign_withSign_not_sign fmt hw₁, ← withSign_not_sign_withSign_not_sign fmt hw₂,
      h.1]

end SoftFloat.Proof
