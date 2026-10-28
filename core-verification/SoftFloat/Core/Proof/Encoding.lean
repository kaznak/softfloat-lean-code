/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators.Sign
import SoftFloat.Core.Spec.Result
import SoftFloat.Core.Spec.Sign

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem sigBits_eq_fracBits_add_one (fmt : Format) : fmt.sigBits = fmt.fracBits + 1 := by
  have := fmt.sigBits_two_le; unfold Format.fracBits; omega

theorem one_le_fracBits (fmt : Format) : 1 ≤ fmt.fracBits := by
  have := fmt.sigBits_two_le; unfold Format.fracBits; omega

theorem width_sub_one (fmt : Format) : fmt.width - 1 = fmt.expBits + fmt.fracBits := by
  have := fmt.sigBits_two_le; unfold Format.width Format.fracBits; omega

theorem width_eq (fmt : Format) : fmt.width = fmt.expBits + fmt.fracBits + 1 := by
  have := fmt.sigBits_two_le; unfold Format.width Format.fracBits; omega

@[simp] theorem isEncoding_iff (fmt : Format) (a : Nat) : fmt.IsEncoding a ↔ a < 2 ^ fmt.width :=
  Iff.rfl

theorem fracBits_cast (fmt : Format) : (fmt.fracBits : Int) = (fmt.sigBits : Int) - 1 := by
  have := (sigBits_eq_fracBits_add_one fmt); omega

theorem expMax_lt (fmt : Format) : fmt.expMax < 2 ^ fmt.expBits := by
  unfold Format.expMax; have := Nat.one_le_two_pow (n := fmt.expBits); omega

theorem expMax_add_one (fmt : Format) : fmt.expMax + 1 = 2 ^ fmt.expBits := by
  unfold Format.expMax; have := Nat.one_le_two_pow (n := fmt.expBits); omega

theorem expMax_ne_zero (fmt : Format) : fmt.expMax ≠ 0 := by
  have h : 2 ^ 2 ≤ 2 ^ fmt.expBits := Nat.pow_le_pow_right (by decide) fmt.expBits_two_le
  unfold Format.expMax; omega

theorem quietBit_pos (fmt : Format) : 0 < fmt.quietBit := by
  unfold Format.quietBit; positivity

theorem quietBit_lt (fmt : Format) : fmt.quietBit < 2 ^ fmt.fracBits := by
  unfold Format.quietBit
  exact Nat.pow_lt_pow_right (by decide) (by have := (one_le_fracBits fmt); omega)

theorem two_pow_fracBits_eq (fmt : Format) :
    2 ^ fmt.fracBits = 2 * fmt.quietBit := by
  unfold Format.quietBit
  have := (one_le_fracBits fmt)
  rw [← pow_succ']; congr 1; omega

theorem pack_eq_add (fmt : Format) (s : Bool) (e f : Nat) :
    fmt.pack s e f = (if s then 2 ^ (fmt.width - 1) else 0) + fmt.pack false e f := by
  unfold Format.pack; rw [(width_sub_one fmt), pow_add]; cases s <;> simp; ring

theorem pack_false_lt (fmt : Format) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    fmt.pack false e f < 2 ^ (fmt.width - 1) := by
  unfold Format.pack; rw [(width_sub_one fmt), pow_add]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add]
  calc e * 2 ^ fmt.fracBits + f < e * 2 ^ fmt.fracBits + 2 ^ fmt.fracBits := by omega
    _ = (e + 1) * 2 ^ fmt.fracBits := by ring
    _ ≤ 2 ^ fmt.expBits * 2 ^ fmt.fracBits := Nat.mul_le_mul_right _ he

theorem pack_lt (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    fmt.pack s e f < 2 ^ fmt.width := by
  have h := pack_false_lt fmt he hf
  have hw : 2 ^ fmt.width = 2 ^ (fmt.width - 1) + 2 ^ (fmt.width - 1) := by
    rw [width_eq fmt, Nat.add_sub_cancel, pow_succ]; ring
  rw [pack_eq_add, hw]; cases s <;> simp <;> omega

theorem unpack_pack (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    fmt.unpack (fmt.pack s e f) = ⟨s, e, f⟩ := by
  have hExpPow : (0 : Nat) < 2 ^ fmt.expBits := by positivity
  have hFracPow : (0 : Nat) < 2 ^ fmt.fracBits := by positivity
  simp only [Format.unpack, Format.pack, Unpacked.mk.injEq, (width_sub_one fmt)]
  have hdiv1 : (((if s then 1 else 0) * 2 ^ fmt.expBits + e) * 2 ^ fmt.fracBits + f)
      / 2 ^ fmt.fracBits = (if s then 1 else 0) * 2 ^ fmt.expBits + e := by
    rw [add_comm, Nat.add_mul_div_right _ _ hFracPow, Nat.div_eq_of_lt hf, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_add, mul_comm (2 ^ fmt.expBits) (2 ^ fmt.fracBits), ← Nat.div_div_eq_div_mul, hdiv1,
      add_comm, Nat.add_mul_div_right _ _ hExpPow, Nat.div_eq_of_lt he, zero_add]
    cases s <;> simp
  · rw [hdiv1, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]

@[simp] theorem unpack_pack_sign (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    (fmt.unpack (fmt.pack s e f)).sign = s := by rw [unpack_pack fmt s he hf]

theorem unpack_pack_expField (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    (fmt.unpack (fmt.pack s e f)).expField = e := by rw [unpack_pack fmt s he hf]

theorem unpack_pack_fracField (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    (fmt.unpack (fmt.pack s e f)).fracField = f := by rw [unpack_pack fmt s he hf]

theorem unpack_expField_lt (fmt : Format) (n : Nat) :
    (fmt.unpack n).expField < 2 ^ fmt.expBits :=
  Nat.mod_lt _ (by positivity)

theorem unpack_fracField_lt (fmt : Format) (n : Nat) :
    (fmt.unpack n).fracField < 2 ^ fmt.fracBits :=
  Nat.mod_lt _ (by positivity)

theorem unpack_sign_eq (fmt : Format) (n : Nat) :
    (fmt.unpack n).sign = decide (n / 2 ^ (fmt.width - 1) % 2 = 1) := by
  simp only [Format.unpack]
  by_cases h : n / 2 ^ (fmt.width - 1) % 2 = 1 <;> simp [h]

theorem pack_unpack (fmt : Format) {n : Nat} (hn : n < 2 ^ fmt.width) :
    fmt.pack (fmt.unpack n).sign (fmt.unpack n).expField (fmt.unpack n).fracField = n := by
  have hM : 0 < 2 ^ fmt.fracBits := by positivity
  have hE : 0 < 2 ^ fmt.expBits := by positivity
  have hq : n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits < 2 := by
    have hw : 2 ^ fmt.width = 2 ^ fmt.fracBits * 2 ^ fmt.expBits * 2 := by
      rw [width_eq fmt, pow_succ, pow_add]; ring
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity), mul_comm]
    rw [hw] at hn; exact hn
  have h01 : n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits = 0 ∨
      n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits = 1 := by
    generalize n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits = q at hq ⊢; omega
  have hsb : (if (fmt.unpack n).sign then 1 else 0) = n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits := by
    simp only [Format.unpack, (width_sub_one fmt), pow_add,
      mul_comm (2 ^ fmt.expBits) (2 ^ fmt.fracBits), ← Nat.div_div_eq_div_mul]
    rcases h01 with h | h <;> rw [h] <;> simp
  unfold Format.pack
  rw [hsb]
  simp only [Format.unpack]
  rw [mul_comm (n / 2 ^ fmt.fracBits / 2 ^ fmt.expBits), Nat.div_add_mod,
    mul_comm (n / 2 ^ fmt.fracBits), Nat.div_add_mod]

theorem unpack_inj (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : fmt.unpack a = fmt.unpack b) : a = b := by
  rw [← pack_unpack fmt ha, ← pack_unpack fmt hb, h]

theorem classify_eq_fields (fmt : Format) (n : Nat) :
    classify fmt n =
      let u := fmt.unpack n
      if u.expField = fmt.expMax then
        if u.fracField ≠ 0 then
          if u.fracField ≥ fmt.quietBit then .quietNaN else .signalingNaN
        else .infinity u.sign
      else if u.expField ≠ 0 then .normal u.sign
      else if u.fracField ≠ 0 then .subnormal u.sign
      else .zero u.sign := rfl

local macro "enc_cases " fmt:term ", " u:term : tactic => `(tactic| (
  have h0 : (0 : Nat) ≠ ($fmt).expMax := Ne.symm (expMax_ne_zero $fmt)
  have h0' : ($fmt).expMax ≠ 0 := expMax_ne_zero $fmt
  by_cases h3 : ($fmt).quietBit ≤ ($u).fracField
  · have h3' : ¬ ($u).fracField < ($fmt).quietBit := Nat.not_lt.mpr h3
    by_cases h1 : ($u).expField = ($fmt).expMax <;>
      by_cases h2 : ($u).fracField = 0 <;>
      by_cases h4 : ($u).expField = 0 <;>
      simp [h0, h0', h1, h2, h3, h3', h4, FloatClass.toClass]
  · have h3' : ($u).fracField < ($fmt).quietBit := Nat.lt_of_not_le h3
    by_cases h1 : ($u).expField = ($fmt).expMax <;>
      by_cases h2 : ($u).fracField = 0 <;>
      by_cases h4 : ($u).expField = 0 <;>
      simp [h0, h0', h1, h2, h3, h3', h4, FloatClass.toClass]))

theorem isSignalingNaN_eq_decide (fmt : Format) (a : Nat) :
    isSignalingNaN fmt a = decide (classify fmt a = .signalingNaN) := by
  unfold isSignalingNaN; cases classify fmt a <;> rfl

theorem isNaNU_unpack (fmt : Format) (a : Nat) : fmt.isNaNU (fmt.unpack a) = isNaN fmt a := by
  unfold isNaN Format.isNaNU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem isSNaNU_unpack (fmt : Format) (a : Nat) :
    fmt.isSNaNU (fmt.unpack a) = isSignalingNaN fmt a := by
  rw [isSignalingNaN_eq_decide]
  unfold Format.isSNaNU Format.isNaNU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem classify_eq_quietNaN_iff (fmt : Format) (a : Nat) :
    classify fmt a = .quietNaN ↔
      fmt.isNaNU (fmt.unpack a) = true ∧ fmt.isSNaNU (fmt.unpack a) = false := by
  unfold Format.isSNaNU Format.isNaNU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem classify_eq_signalingNaN_iff (fmt : Format) (a : Nat) :
    classify fmt a = .signalingNaN ↔ fmt.isSNaNU (fmt.unpack a) = true := by
  rw [isSNaNU_unpack, isSignalingNaN_eq_decide, decide_eq_true_iff]

theorem isNaN_iff (fmt : Format) (a : Nat) :
    isNaN fmt a = true ↔ classify fmt a = .quietNaN ∨ classify fmt a = .signalingNaN := by
  unfold isNaN; cases classify fmt a <;> simp

theorem classify_eq_infinity_iff (fmt : Format) (a : Nat) (s : Bool) :
    classify fmt a = .infinity s ↔ fmt.isInfU (fmt.unpack a) = true ∧ (fmt.unpack a).sign = s := by
  unfold Format.isInfU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem isInfU_unpack_iff (fmt : Format) (a : Nat) :
    fmt.isInfU (fmt.unpack a) = true ↔ classify fmt a = .infinity (fmt.unpack a).sign := by
  simp [classify_eq_infinity_iff]

theorem classify_eq_zero_iff (fmt : Format) (a : Nat) (s : Bool) :
    classify fmt a = .zero s ↔ isZeroU (fmt.unpack a) = true ∧ (fmt.unpack a).sign = s := by
  unfold Format.isZeroU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem isZeroU_unpack_iff (fmt : Format) (a : Nat) :
    isZeroU (fmt.unpack a) = true ↔ classify fmt a = .zero (fmt.unpack a).sign := by
  simp [classify_eq_zero_iff]

theorem classify_eq_normal_iff (fmt : Format) (a : Nat) (s : Bool) :
    classify fmt a = .normal s ↔ fmt.isNormalU (fmt.unpack a) = true ∧ (fmt.unpack a).sign = s := by
  unfold Format.isNormalU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem isNormalU_unpack_iff (fmt : Format) (a : Nat) :
    fmt.isNormalU (fmt.unpack a) = true ↔ classify fmt a = .normal (fmt.unpack a).sign := by
  simp [classify_eq_normal_iff]

theorem classify_eq_subnormal_iff (fmt : Format) (a : Nat) (s : Bool) :
    classify fmt a = .subnormal s ↔
      isSubnormalU (fmt.unpack a) = true ∧ (fmt.unpack a).sign = s := by
  unfold Format.isSubnormalU; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack a

theorem isSubnormalU_unpack_iff (fmt : Format) (a : Nat) :
    isSubnormalU (fmt.unpack a) = true ↔ classify fmt a = .subnormal (fmt.unpack a).sign := by
  simp [classify_eq_subnormal_iff]

theorem classOf_eq_toClass (fmt : Format) (n : Nat) :
    fmt.classOf n = (classify fmt n).toClass := by
  unfold Format.classOf Format.isSNaNU Format.isNaNU Format.isInfU Format.isZeroU
    Format.isSubnormalU
  rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack n

theorem classSpecOf_classOf (fmt : Format) (n : Nat) : ClassSpecOf fmt n (fmt.classOf n) :=
  classOf_eq_toClass fmt n

theorem isFinite_iff (fmt : Format) (n : Nat) :
    IsFinite fmt n ↔ (fmt.unpack n).expField ≠ fmt.expMax := by
  unfold IsFinite; rw [classify_eq_fields]; dsimp only
  enc_cases fmt, fmt.unpack n

instance (fmt : Format) (n : Nat) : Decidable (IsFinite fmt n) :=
  decidable_of_iff _ (isFinite_iff fmt n).symm

theorem isFinite_iff_not_isNaN_not_isInf (fmt : Format) (n : Nat) :
    IsFinite fmt n ↔ isNaN fmt n = false ∧ ∀ s, classify fmt n ≠ .infinity s := by
  unfold IsFinite isNaN; cases classify fmt n <;> simp

theorem valE_of_isFinite (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    valE fmt n = (valR fmt n : EReal) := by
  unfold valE; unfold IsFinite at h; split <;> simp_all

theorem isNaN_eq_false_of_isFinite (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    isNaN fmt n = false :=
  ((isFinite_iff_not_isNaN_not_isInf fmt n).1 h).1

theorem isNaNU_eq_false_of_isFinite (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    fmt.isNaNU (fmt.unpack n) = false := by
  rw [isNaNU_unpack]; exact isNaN_eq_false_of_isFinite fmt h

theorem isInfU_eq_false_of_isFinite (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    fmt.isInfU (fmt.unpack n) = false := by
  have := (isFinite_iff fmt n).1 h
  unfold Format.isInfU; simp [this]

theorem exists_infinity_of_not_isFinite (fmt : Format) {n : Nat} (hn : isNaN fmt n = false)
    (hf : ¬ IsFinite fmt n) : ∃ s, classify fmt n = .infinity s := by
  by_contra hc
  push Not at hc
  exact hf ((isFinite_iff_not_isNaN_not_isInf fmt n).2 ⟨hn, hc⟩)

theorem sigOf_eq_zero_iff (fmt : Format) (u : Unpacked) : fmt.sigOf u = 0 ↔ isZeroU u = true := by
  have : 0 < 2 ^ fmt.fracBits := by positivity
  unfold Format.sigOf Format.isZeroU
  split_ifs with h <;> simp [h]

theorem sigOf_pos (fmt : Format) {u : Unpacked} (h : isZeroU u = false) : 0 < fmt.sigOf u := by
  rcases Nat.eq_zero_or_pos (fmt.sigOf u) with h0 | h0
  · rw [sigOf_eq_zero_iff] at h0; simp_all
  · exact h0

section PackClassify

variable (fmt : Format) (s : Bool) {e f : Nat}

theorem classify_pack (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    classify fmt (fmt.pack s e f) =
      if e = fmt.expMax then
        if f ≠ 0 then (if f ≥ fmt.quietBit then .quietNaN else .signalingNaN)
        else .infinity s
      else if e ≠ 0 then .normal s
      else if f ≠ 0 then .subnormal s
      else .zero s := by
  rw [classify_eq_fields, unpack_pack fmt s he hf]

theorem classify_pack_infinity : classify fmt (fmt.pack s fmt.expMax 0) = .infinity s := by
  rw [classify_pack fmt s (expMax_lt fmt) (by positivity)]; simp

theorem classify_pack_quietNaN (hf : f < 2 ^ fmt.fracBits) (hq : fmt.quietBit ≤ f) :
    classify fmt (fmt.pack s fmt.expMax f) = .quietNaN := by
  have := (quietBit_pos fmt)
  rw [classify_pack fmt s (expMax_lt fmt) hf]; simp [hq]; omega

theorem classify_pack_signalingNaN (hf0 : f ≠ 0) (hq : f < fmt.quietBit) :
    classify fmt (fmt.pack s fmt.expMax f) = .signalingNaN := by
  have := (quietBit_lt fmt)
  rw [classify_pack fmt s (expMax_lt fmt) (by omega)]; simp [hf0]; omega

theorem classify_pack_normal (he0 : e ≠ 0) (he : e < fmt.expMax) (hf : f < 2 ^ fmt.fracBits) :
    classify fmt (fmt.pack s e f) = .normal s := by
  have := (expMax_lt fmt)
  rw [classify_pack fmt s (by omega) hf]; simp [he0, Nat.ne_of_lt he]

theorem classify_pack_subnormal (hf0 : f ≠ 0) (hf : f < 2 ^ fmt.fracBits) :
    classify fmt (fmt.pack s 0 f) = .subnormal s := by
  have := (expMax_ne_zero fmt)
  rw [classify_pack fmt s (by positivity) hf]; simp [hf0, Ne.symm this]

theorem classify_pack_zero : classify fmt (fmt.pack s 0 0) = .zero s := by
  have := (expMax_ne_zero fmt)
  rw [classify_pack fmt s (by positivity) (by positivity)]; simp [Ne.symm this]

theorem isFinite_pack (he : e < fmt.expMax) (hf : f < 2 ^ fmt.fracBits) :
    IsFinite fmt (fmt.pack s e f) := by
  have := (expMax_lt fmt)
  rw [isFinite_iff, unpack_pack fmt s (by omega) hf]; exact Nat.ne_of_lt he

end PackClassify

theorem pack_expMax_lt (fmt : Format) (s : Bool) : fmt.pack s fmt.expMax 0 < 2 ^ fmt.width :=
  pack_lt fmt s (expMax_lt fmt) (by positivity)

theorem pack_zero_lt (fmt : Format) (s : Bool) : fmt.pack s 0 0 < 2 ^ fmt.width :=
  pack_lt fmt s (by positivity) (by positivity)

theorem valR_eq_sigOf (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    valR fmt n = (if (fmt.unpack n).sign then -1 else 1)
      * ((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) := by
  have hfc := fracBits_cast fmt
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  unfold IsFinite at h
  unfold valR emin emax
  dsimp only
  cases hc : classify fmt n with
  | normal t =>
    have hn := (classify_eq_normal_iff fmt n t).1 hc
    unfold Format.isNormalU at hn
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    simp only [Format.sigOf, Format.ulpExpOf, hn.1.1, ↓reduceIte]
    rw [show ((fmt.unpack n).expField : Int) - (fmt.bias : Int) - fmt.fracBits
        = ((fmt.unpack n).expField - (fmt.bias : Int)) + (1 - (fmt.sigBits : Int)) by omega,
      zpow_add₀ h2]
    have hp : ((2 : ℝ) ^ (1 - (fmt.sigBits : Int))) * (2 : ℝ) ^ fmt.fracBits = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ h2, show 1 - (fmt.sigBits : Int) + fmt.fracBits = 0 by
        omega, zpow_zero]
    push_cast
    linear_combination (-(if (fmt.unpack n).sign = true then (-1 : ℝ) else 1)) *
      (2 : ℝ) ^ (((fmt.unpack n).expField : Int) - (fmt.bias : Int)) * hp
  | subnormal t =>
    have hn := (classify_eq_subnormal_iff fmt n t).1 hc
    unfold Format.isSubnormalU at hn
    simp only [Bool.and_eq_true, beq_iff_eq] at hn
    simp only [Format.sigOf, Format.ulpExpOf, hn.1.1, ↓reduceIte]
    rw [show (1 : Int) - (fmt.bias : Int) - fmt.fracBits
        = (1 - (fmt.bias : Int)) + (1 - (fmt.sigBits : Int)) by omega, zpow_add₀ h2]
    ring
  | zero t =>
    have hn := (classify_eq_zero_iff fmt n t).1 hc
    unfold Format.isZeroU at hn
    simp only [Bool.and_eq_true, beq_iff_eq] at hn
    simp [Format.sigOf, hn.1.1, hn.1.2]
  | quietNaN => rw [hc] at h; exact h.elim
  | signalingNaN => rw [hc] at h; exact h.elim
  | infinity t => rw [hc] at h; exact h.elim

theorem valR_of_not_isFinite (fmt : Format) {n : Nat} (h : ¬ IsFinite fmt n) : valR fmt n = 0 := by
  unfold valR; unfold IsFinite at h; split <;> simp_all

section PackValue

variable (fmt : Format) (s : Bool) {e f : Nat}

theorem valR_pack_normal (he0 : e ≠ 0) (he : e < fmt.expMax) (hf : f < 2 ^ fmt.fracBits) :
    valR fmt (fmt.pack s e f) = (if s then -1 else 1)
      * (2 : ℝ) ^ ((e : Int) - (fmt.bias : Int)) * (1 + (2 : ℝ) ^ (1 - (fmt.sigBits : Int)) * f) := by
  have := (expMax_lt fmt)
  unfold valR
  rw [classify_pack_normal fmt s he0 he hf, unpack_pack fmt s (by omega) hf]

theorem valR_pack_normal_sig (he0 : e ≠ 0) (he : e < fmt.expMax) (hf : f < 2 ^ fmt.fracBits) :
    valR fmt (fmt.pack s e f) = (if s then -1 else 1)
      * (((2 ^ fmt.fracBits + f : Nat)) : ℝ)
      * (2 : ℝ) ^ ((e : Int) - (fmt.bias : Int) - (fmt.fracBits : Int)) := by
  have := (expMax_lt fmt)
  rw [valR_eq_sigOf fmt (isFinite_pack fmt s he hf), unpack_pack fmt s (by omega) hf]
  simp [Format.sigOf, Format.ulpExpOf, he0]

theorem valR_pack_subnormal (hf : f < 2 ^ fmt.fracBits) :
    valR fmt (fmt.pack s 0 f) = (if s then -1 else 1) * (f : ℝ) * (2 : ℝ) ^ fmt.minQ := by
  rw [valR_eq_sigOf fmt (isFinite_pack fmt s (Nat.pos_of_ne_zero (expMax_ne_zero fmt)) hf),
    unpack_pack fmt s (by positivity) hf]
  simp [Format.sigOf, Format.ulpExpOf, Format.minQ]

theorem valR_pack_zero : valR fmt (fmt.pack s 0 0) = 0 := by
  rw [valR_pack_subnormal fmt s (by positivity)]; simp

theorem valR_eq_zero_iff (n : Nat) :
    valR fmt n = 0 ↔ ¬ IsFinite fmt n ∨ ∃ s, classify fmt n = .zero s := by
  by_cases h : IsFinite fmt n
  · rw [valR_eq_sigOf fmt h]
    simp only [h, not_true_eq_false, false_or]
    rw [isFinite_iff] at h
    have h2 : (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) ≠ 0 := by positivity
    constructor
    · intro hv
      have hs : ((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) = 0 := by
        rcases mul_eq_zero.mp hv with hv | hv
        · rcases mul_eq_zero.mp hv with hv | hv
          · split_ifs at hv <;> norm_num at hv
          · exact hv
        · exact absurd hv h2
      have hs' : fmt.sigOf (fmt.unpack n) = 0 := by exact_mod_cast hs
      unfold Format.sigOf at hs'
      refine ⟨(fmt.unpack n).sign, ?_⟩
      rw [classify_eq_zero_iff]; unfold Format.isZeroU
      split_ifs at hs' with he
      · simp [he, hs']
      · have : 0 < 2 ^ fmt.fracBits := by positivity
        omega
    · rintro ⟨t, ht⟩
      rw [classify_eq_zero_iff] at ht; unfold Format.isZeroU at ht
      simp only [Bool.and_eq_true, beq_iff_eq] at ht
      simp [Format.sigOf, ht.1.1, ht.1.2]
  · simp [h, valR_of_not_isFinite fmt h]

end PackValue

theorem signBitOf_eq (fmt : Format) (n : Nat) :
    fmt.signBitOf n = if (fmt.unpack n).sign then 1 else 0 := by
  unfold Format.signBitOf; simp only [Format.unpack]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ (fmt.width - 1)) with h | h <;> simp [h]

theorem clearSign_pack (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    fmt.clearSign (fmt.pack s e f) = fmt.pack false e f := by
  unfold Format.clearSign
  have h := pack_false_lt fmt he hf
  rw [pack_eq_add]; cases s <;> simp [Nat.mod_eq_of_lt h]

theorem flipSign_pack (fmt : Format) (s : Bool) {e f : Nat}
    (he : e < 2 ^ fmt.expBits) (hf : f < 2 ^ fmt.fracBits) :
    fmt.flipSign (fmt.pack s e f) = fmt.pack (!s) e f := by
  unfold Format.flipSign
  have h := pack_false_lt fmt he hf
  rw [pack_eq_add fmt s, pack_eq_add fmt (!s)]
  cases s <;> simp [h, add_comm]

theorem withSign_eq (fmt : Format) (x : Nat) (s : Bool) :
    withSign fmt x s = fmt.pack s (fmt.unpack x).expField (fmt.unpack x).fracField := rfl

theorem unpack_withSign (fmt : Format) (x : Nat) (s : Bool) :
    fmt.unpack (withSign fmt x s) = { fmt.unpack x with sign := s } :=
  unpack_pack fmt s (unpack_expField_lt fmt x) (unpack_fracField_lt fmt x)

theorem withSign_lt (fmt : Format) (x : Nat) (s : Bool) : withSign fmt x s < 2 ^ fmt.width :=
  pack_lt fmt s (unpack_expField_lt fmt x) (unpack_fracField_lt fmt x)

theorem withSign_self (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    withSign fmt x (fmt.unpack x).sign = x :=
  pack_unpack fmt hx

theorem flipSign_eq_withSign (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    fmt.flipSign x = withSign fmt x (!(fmt.unpack x).sign) := by
  conv_lhs => rw [← pack_unpack fmt hx]
  exact flipSign_pack fmt _ (unpack_expField_lt fmt x) (unpack_fracField_lt fmt x)

theorem clearSign_eq_withSign (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    fmt.clearSign x = withSign fmt x false := by
  conv_lhs => rw [← pack_unpack fmt hx]
  exact clearSign_pack fmt _ (unpack_expField_lt fmt x) (unpack_fracField_lt fmt x)

theorem copySign_eq_withSign (fmt : Format) {a : Nat} (ha : a < 2 ^ fmt.width) (b : Nat) :
    fmt.copySign a b = withSign fmt a (fmt.unpack b).sign := by
  unfold Format.copySign
  rw [clearSign_eq_withSign fmt ha, signBitOf_eq, withSign_eq, withSign_eq,
    pack_eq_add fmt (fmt.unpack b).sign]
  cases (fmt.unpack b).sign <;> simp [add_comm]

theorem classify_withSign (fmt : Format) (x : Nat) (s : Bool) :
    classify fmt (withSign fmt x s) =
      match classify fmt x with
      | .infinity _ => .infinity s
      | .normal _ => .normal s
      | .subnormal _ => .subnormal s
      | .zero _ => .zero s
      | c => c := by
  rw [classify_eq_fields fmt (withSign fmt x s), unpack_withSign, classify_eq_fields fmt x]
  dsimp only
  split_ifs <;> rfl

theorem valR_withSign (fmt : Format) (x : Nat) (s : Bool) :
    valR fmt (withSign fmt x s) =
      if s = (fmt.unpack x).sign then valR fmt x else -valR fmt x := by
  unfold valR
  rw [classify_withSign, unpack_withSign]; dsimp only
  cases hc : classify fmt x <;> cases s <;> cases (fmt.unpack x).sign <;> simp

end SoftFloat.Proof
