/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Common
import SoftFloat.Core.Proof.TotalOrder

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem natCast_two_pow_sub_mul_zpow (fmt : Format) {k c : Nat} (hk : k ≤ fmt.fracBits) :
    ((2 ^ (fmt.fracBits - k) * c : Nat) : ℝ) * (2 : ℝ) ^ ((k : Int) - (fmt.fracBits : Int)) = c := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  push_cast
  rw [mul_comm ((2 : ℝ) ^ (fmt.fracBits - k)), mul_assoc, ← zpow_natCast, ← zpow_add₀ h2,
    show ((fmt.fracBits - k : Nat) : Int) + ((k : Int) - (fmt.fracBits : Int)) = 0 by omega,
    zpow_zero, mul_one]

theorem pack_false_zero_zero (fmt : Format) : fmt.pack false 0 0 = 0 := by
  simp [Format.pack]

theorem classify_zero (fmt : Format) : classify fmt 0 = .zero false := by
  simpa [pack_false_zero_zero] using classify_pack_zero fmt false

theorem unpack_zero (fmt : Format) : fmt.unpack 0 = ⟨false, 0, 0⟩ := by
  simpa [pack_false_zero_zero] using unpack_pack fmt false (e := 0) (f := 0) (by positivity) (by positivity)

theorem ofNatExact_spec (fmt : Format) {n : Nat} (hn : n < 2 ^ fmt.fracBits) :
    fmt.ofNatExact n < 2 ^ fmt.width ∧ IsNonNegativeIntegerOf fmt (fmt.ofNatExact n) n := by
  have hb := fmt.fracBits_le_bias
  have hf1 := one_le_fracBits fmt
  have hE := expMax_eq_two_mul_bias_add_one fmt
  have hEl := expMax_lt fmt
  unfold Format.ofNatExact
  split_ifs with h0
  · subst h0
    have hz := classify_zero fmt
    refine ⟨by positivity, by unfold IsFinite; rw [hz]; trivial, by rw [unpack_zero], ?_⟩
    rw [(valR_eq_zero_iff fmt 0).2 (Or.inr ⟨false, hz⟩)]; simp
  · have hk1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le h0
    have hk2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have hkf : n.log2 < fmt.fracBits := (Nat.log2_lt h0).2 hn
    have hsplit : 2 ^ fmt.fracBits = 2 ^ n.log2 * 2 ^ (fmt.fracBits - n.log2) := by
      rw [← pow_add]; congr 1; omega
    have hf : (n - 2 ^ n.log2) * 2 ^ (fmt.fracBits - n.log2) < 2 ^ fmt.fracBits := by
      rw [hsplit]
      exact Nat.mul_lt_mul_of_pos_right (by rw [pow_succ] at hk2; omega) (by positivity)
    have he0 : fmt.bias + n.log2 ≠ 0 := by omega
    have he : fmt.bias + n.log2 < fmt.expMax := by omega
    refine ⟨pack_lt fmt false (by omega) hf, isFinite_pack fmt false he hf,
      unpack_pack_sign fmt false (by omega) hf, ?_⟩
    rw [valR_pack_normal_sig fmt false he0 he hf]
    have hsum : 2 ^ fmt.fracBits + (n - 2 ^ n.log2) * 2 ^ (fmt.fracBits - n.log2)
        = 2 ^ (fmt.fracBits - n.log2) * n := by
      rw [hsplit, Nat.mul_sub_right_distrib, Nat.mul_comm (2 ^ (fmt.fracBits - n.log2)) n]
      have := Nat.mul_le_mul_right (2 ^ (fmt.fracBits - n.log2)) hk1
      omega
    rw [hsum, show (((fmt.bias + n.log2 : Nat) : Int) - (fmt.bias : Int) - (fmt.fracBits : Int))
      = (n.log2 : Int) - (fmt.fracBits : Int) by push_cast; ring]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact natCast_two_pow_sub_mul_zpow fmt hkf.le

theorem minusOne_spec (fmt : Format) :
    fmt.minusOne < 2 ^ fmt.width ∧ IsFinite fmt fmt.minusOne ∧ valR fmt fmt.minusOne = -1 := by
  have hb := fmt.fracBits_le_bias
  have hf1 := one_le_fracBits fmt
  have hE := expMax_eq_two_mul_bias_add_one fmt
  have hEl := expMax_lt fmt
  have he0 : fmt.bias ≠ 0 := by omega
  have he : fmt.bias < fmt.expMax := by omega
  unfold Format.minusOne
  refine ⟨pack_lt fmt true (by omega) (by positivity), isFinite_pack fmt true he (by positivity), ?_⟩
  rw [valR_pack_normal fmt true he0 he (by positivity)]
  simp

theorem payloadOfInteger_eq_some {fmt : Format} {a n : Nat} (h : fmt.payloadOfInteger a = some n) :
    IsNonNegativeIntegerOf fmt a n ∧ n < 2 ^ (fmt.fracBits - 1) := by
  have hb := fmt.fracBits_le_bias
  have hE := expMax_eq_two_mul_bias_add_one fmt
  unfold Format.payloadOfInteger at h
  simp only at h
  split_ifs at h with hs he hf hc
  · cases h
    have hz : classify fmt a = .zero false :=
      (classify_eq_zero_iff fmt a false).2 ⟨by simp [Format.isZeroU, he, hf], by simpa using hs⟩
    refine ⟨⟨by unfold IsFinite; rw [hz]; trivial, by simpa using hs,
      by rw [(valR_eq_zero_iff fmt a).2 (Or.inr ⟨false, hz⟩)]; simp⟩, by positivity⟩
  · cases h
    obtain ⟨hbe, hk, hmod⟩ := hc
    set e := (fmt.unpack a).expField with he_def
    set f := (fmt.unpack a).fracField with hf_def
    set k := e - fmt.bias with hk_def
    have hfin : IsFinite fmt a := by rw [isFinite_iff]; omega
    have hflt : f < 2 ^ fmt.fracBits := unpack_fracField_lt fmt a
    have hsplit : 2 ^ fmt.fracBits = 2 ^ (fmt.fracBits - k) * 2 ^ k := by
      rw [← pow_add]; congr 1; omega
    have hfq : f = 2 ^ (fmt.fracBits - k) * (f / 2 ^ (fmt.fracBits - k)) :=
      (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
    have hq : f / 2 ^ (fmt.fracBits - k) < 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hsplit]; exact hflt
    refine ⟨⟨hfin, by simpa using hs, ?_⟩, ?_⟩
    · rw [valR_eq_sigOf fmt hfin]
      simp only [show (fmt.unpack a).sign = false by simpa using hs, Bool.false_eq_true, ↓reduceIte,
        one_mul, Format.sigOf, Format.ulpExpOf, ← he_def, he]
      have hsum : 2 ^ fmt.fracBits + f
          = 2 ^ (fmt.fracBits - k) * (2 ^ k + f / 2 ^ (fmt.fracBits - k)) := by
        rw [hsplit, Nat.mul_add]; omega
      rw [hsum, show (e : Int) - (fmt.bias : Int) - (fmt.fracBits : Int)
        = (k : Int) - (fmt.fracBits : Int) by omega]
      exact natCast_two_pow_sub_mul_zpow fmt (by omega)
    · calc 2 ^ k + f / 2 ^ (fmt.fracBits - k) < 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ (fmt.fracBits - 1) := Nat.pow_le_pow_right (by decide) (by omega)

theorem payloadOfInteger_ofNatExact (fmt : Format) {n : Nat} (hn : n < 2 ^ (fmt.fracBits - 1)) :
    fmt.payloadOfInteger (fmt.ofNatExact n) = some n := by
  have hb := fmt.fracBits_le_bias
  have hf1 : 2 ≤ fmt.fracBits := by have := fmt.sigBits_three_le; unfold Format.fracBits; omega
  have hE := expMax_eq_two_mul_bias_add_one fmt
  have hEl := expMax_lt fmt
  unfold Format.ofNatExact
  split_ifs with h0
  · subst h0
    unfold Format.payloadOfInteger
    rw [unpack_zero]
    simp
  · have hk1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le h0
    have hk2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have hkf : n.log2 < fmt.fracBits - 1 := (Nat.log2_lt h0).2 hn
    have hsplit : 2 ^ fmt.fracBits = 2 ^ n.log2 * 2 ^ (fmt.fracBits - n.log2) := by
      rw [← pow_add]; congr 1; omega
    have hf : (n - 2 ^ n.log2) * 2 ^ (fmt.fracBits - n.log2) < 2 ^ fmt.fracBits := by
      rw [hsplit]
      exact Nat.mul_lt_mul_of_pos_right (by rw [pow_succ] at hk2; omega) (by positivity)
    unfold Format.payloadOfInteger
    rw [unpack_pack fmt false (by omega) hf]
    have hk : fmt.bias + n.log2 - fmt.bias = n.log2 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hk, Nat.mul_mod_left, Nat.mul_div_cancel _
      (Nat.two_pow_pos _)]
    have hne : ¬ (fmt.bias + n.log2 = 0) := by omega
    have hc : fmt.bias ≤ fmt.bias + n.log2 ∧ n.log2 + 1 < fmt.fracBits ∧ True := ⟨by omega, by omega, trivial⟩
    simp only [hne, hc, ↓reduceIte, and_self]
    congr 1; omega

theorem payloadOfInteger_of_isNonNegativeIntegerOf {fmt : Format} {a n : Nat}
    (ha : a < 2 ^ fmt.width) (h : IsNonNegativeIntegerOf fmt a n) (hn : n < 2 ^ (fmt.fracBits - 1)) :
    fmt.payloadOfInteger a = some n := by
  obtain ⟨hfin, hs, hv⟩ := h
  by_cases h0 : n = 0
  · subst h0
    obtain ⟨s, hz⟩ := ((valR_eq_zero_iff fmt a).1 (by simpa using hv)).resolve_left (not_not.2 hfin)
    obtain ⟨hzu, -⟩ := (classify_eq_zero_iff fmt a s).1 hz
    unfold Format.isZeroU at hzu
    simp only [Bool.and_eq_true, beq_iff_eq] at hzu
    unfold Format.payloadOfInteger
    simp [hs, hzu.1, hzu.2]
  · have hlt : n < 2 ^ fmt.fracBits :=
      lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    obtain ⟨hw, hfin', -, hv'⟩ := ofNatExact_spec fmt hlt
    have heq : a = fmt.ofNatExact n :=
      eq_of_valR_eq fmt ha hw hfin hfin' (hv.trans hv'.symm) (by rw [hv]; exact_mod_cast h0)
    rw [heq]; exact payloadOfInteger_ofNatExact fmt hn

theorem not_isAdmissiblePayload_of_payloadOfInteger_eq_none {sp : Specialization}
    (hsp : Specialization.Valid sp) {fmt : Format} {a : Nat}
    (ha : a < 2 ^ fmt.width) (h : fmt.payloadOfInteger a = none) (signaling : Bool) :
    ∀ n, IsNonNegativeIntegerOf fmt a n → ¬ IsAdmissiblePayload sp fmt signaling n := by
  intro n hn hadm
  rw [payloadOfInteger_of_isNonNegativeIntegerOf ha hn (hsp.admissiblePayload _ _ _ hadm).1] at h
  cases h

theorem eq_of_isNonNegativeIntegerOf_of_isNonNegativeIntegerOf {fmt : Format} {a m n : Nat}
    (h : IsNonNegativeIntegerOf fmt a m) (h' : IsNonNegativeIntegerOf fmt a n) : m = n := by
  have := h.2.2.symm.trans h'.2.2
  exact_mod_cast this

theorem getPayloadSpecOf_getPayload (fmt : Format) (x : Nat) :
    GetPayloadSpecOf fmt x (fmt.getPayload x) := by
  unfold GetPayloadSpecOf Format.getPayload
  simp only [isNaNU_unpack]
  cases h : isNaN fmt x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨(minusOne_spec fmt).1, trivial, (minusOne_spec fmt).2⟩
  · simp only [↓reduceIte]
    have hp : (fmt.unpack x).fracField % fmt.quietBit < 2 ^ fmt.fracBits :=
      lt_trans (Nat.mod_lt _ (quietBit_pos fmt)) (quietBit_lt fmt)
    exact ⟨(ofNatExact_spec fmt hp).1, trivial, (ofNatExact_spec fmt hp).2⟩

theorem setPayloadSpecOf_setPayload (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format)
    {x : Nat} (hx : x < 2 ^ fmt.width) : SetPayloadSpecOf sp fmt x (Format.setPayload sp fmt x) := by
  unfold SetPayloadSpecOf setPayloadResultOf Format.setPayload
  cases h : fmt.payloadOfInteger x with
  | none =>
    dsimp only
    exact ⟨Nat.two_pow_pos _, rfl,
      fun n hn hadm => absurd hadm (not_isAdmissiblePayload_of_payloadOfInteger_eq_none hsp hx h _ n hn),
      fun _ => classify_zero fmt⟩
  | some n =>
    dsimp only
    obtain ⟨hn, hlt⟩ := payloadOfInteger_eq_some h
    by_cases hadm : sp.admissiblePayload false fmt n = true
    · simp only [hadm, ↓reduceIte]
      have hq : fmt.quietBit + n < 2 ^ fmt.fracBits := by
        rw [two_pow_fracBits_eq]; unfold Format.quietBit; omega
      refine ⟨pack_lt fmt _ (expMax_lt fmt) hq, trivial, fun m hm _ => ?_,
        fun hno => absurd hadm (hno n hn)⟩
      rw [eq_of_isNonNegativeIntegerOf_of_isNonNegativeIntegerOf hm hn]
      refine ⟨classify_pack_quietNaN fmt _ hq (Nat.le_add_right _ _),
        unpack_pack_sign fmt _ (expMax_lt fmt) hq, ?_⟩
      unfold nanPayload
      rw [unpack_pack_fracField fmt _ (expMax_lt fmt) hq]
      change (2 ^ (fmt.fracBits - 1) + n) % 2 ^ (fmt.fracBits - 1) = n
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    · simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      refine ⟨Nat.two_pow_pos _, trivial, fun m hm hadm' => ?_, fun _ => classify_zero fmt⟩
      rw [eq_of_isNonNegativeIntegerOf_of_isNonNegativeIntegerOf hm hn] at hadm'
      exact absurd hadm' hadm

theorem setPayloadSignalingSpecOf_setPayloadSignaling (sp : Specialization) (hsp : Specialization.Valid sp)
    (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    SetPayloadSignalingSpecOf sp fmt x (Format.setPayloadSignaling sp fmt x) := by
  unfold SetPayloadSignalingSpecOf setPayloadResultOf Format.setPayloadSignaling
  cases h : fmt.payloadOfInteger x with
  | none =>
    dsimp only
    exact ⟨Nat.two_pow_pos _, rfl,
      fun n hn hadm => absurd hadm (not_isAdmissiblePayload_of_payloadOfInteger_eq_none hsp hx h _ n hn),
      fun _ => classify_zero fmt⟩
  | some n =>
    dsimp only
    obtain ⟨hn, hlt⟩ := payloadOfInteger_eq_some h
    by_cases hadm : sp.admissiblePayload true fmt n = true
    · simp only [hadm, ↓reduceIte]
      have h0 : n ≠ 0 := (hsp.admissiblePayload true fmt n hadm).2 rfl
      have hq : n < fmt.quietBit := hlt
      have hf : n < 2 ^ fmt.fracBits := lt_trans hq (quietBit_lt fmt)
      refine ⟨pack_lt fmt _ (expMax_lt fmt) hf, trivial, fun m hm _ => ?_,
        fun hno => absurd hadm (hno n hn)⟩
      rw [eq_of_isNonNegativeIntegerOf_of_isNonNegativeIntegerOf hm hn]
      refine ⟨classify_pack_signalingNaN fmt _ h0 hq,
        unpack_pack_sign fmt _ (expMax_lt fmt) hf, ?_⟩
      unfold nanPayload
      rw [unpack_pack_fracField fmt _ (expMax_lt fmt) hf]
      exact Nat.mod_eq_of_lt hlt
    · simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      refine ⟨Nat.two_pow_pos _, trivial, fun m hm hadm' => ?_, fun _ => classify_zero fmt⟩
      rw [eq_of_isNonNegativeIntegerOf_of_isNonNegativeIntegerOf hm hn] at hadm'
      exact absurd hadm' hadm

theorem softfloat_getPayload_spec (sp : Specialization) :
    ∀ fmt x, x < 2 ^ fmt.width → GetPayloadSpecOf fmt x ((softfloat sp).getPayload fmt x) :=
  fun fmt x _ => getPayloadSpecOf_getPayload fmt x

theorem softfloat_setPayload_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt x, x < 2 ^ fmt.width → SetPayloadSpecOf sp fmt x ((softfloat sp).setPayload fmt x) :=
  fun fmt _ hx => setPayloadSpecOf_setPayload sp hsp fmt hx

theorem softfloat_setPayloadSignaling_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt x, x < 2 ^ fmt.width →
      SetPayloadSignalingSpecOf sp fmt x ((softfloat sp).setPayloadSignaling fmt x) :=
  fun fmt _ hx => setPayloadSignalingSpecOf_setPayloadSignaling sp hsp fmt hx

theorem eq_of_isNonNegativeIntegerOf {fmt : Format} {a b n : Nat} (ha : a < 2 ^ fmt.width)
    (hb : b < 2 ^ fmt.width) (h₁ : IsNonNegativeIntegerOf fmt a n)
    (h₂ : IsNonNegativeIntegerOf fmt b n) : a = b := by
  obtain ⟨hfa, hsa, hva⟩ := h₁
  obtain ⟨hfb, hsb, hvb⟩ := h₂
  by_cases h0 : (n : ℝ) = 0
  · have hz : ∀ c, c < 2 ^ fmt.width → IsFinite fmt c → (fmt.unpack c).sign = false →
        valR fmt c = 0 → classify fmt c = .zero false := by
      intro c _ hfc hsc hvc
      obtain ⟨s, hs⟩ := ((valR_eq_zero_iff fmt c).1 hvc).resolve_left (not_not.2 hfc)
      have := ((classify_eq_zero_iff fmt c s).1 hs).2
      rw [hsc] at this; rw [hs, ← this]
    exact eq_of_classify_eq_zero fmt ha hb (hz a ha hfa hsa (hva.trans h0))
      (hz b hb hfb hsb (hvb.trans h0))
  · exact eq_of_valR_eq fmt ha hb hfa hfb (hva.trans hvb.symm) (hva ▸ h0)

theorem eq_of_nanPayload_eq {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width)
    (hb : b < 2 ^ fmt.width) (hna : isNaN fmt a = true) (hc : classify fmt a = classify fmt b)
    (hs : (fmt.unpack a).sign = (fmt.unpack b).sign) (hp : nanPayload fmt a = nanPayload fmt b) :
    a = b := by
  have hnb : isNaN fmt b = true := by unfold isNaN at hna ⊢; rw [← hc]; exact hna
  have hq : fmt.quietBit ≤ (fmt.unpack a).fracField ↔ fmt.quietBit ≤ (fmt.unpack b).fracField := by
    have hca := classify_of_isNaN fmt hna
    have hcb := classify_of_isNaN fmt hnb
    by_cases h₁ : fmt.quietBit ≤ (fmt.unpack a).fracField <;>
      by_cases h₂ : fmt.quietBit ≤ (fmt.unpack b).fracField <;> simp_all
    omega
  have hf : (fmt.unpack a).fracField = (fmt.unpack b).fracField :=
    le_antisymm ((nanPayload_le_iff fmt hq).1 hp.le) ((nanPayload_le_iff fmt hq.symm).1 hp.ge)
  refine eq_of_sign_eq_of_orderKeyU_eq fmt ha hb hs ?_
  unfold Format.orderKeyU
  rw [(nan_fields fmt hna).1, (nan_fields fmt hnb).1, hf]

theorem getPayloadSpecOf_unique {fmt : Format} {x : Nat} {r₁ r₂ : Nat × StatusFlags}
    (h₁ : GetPayloadSpecOf fmt x r₁) (h₂ : GetPayloadSpecOf fmt x r₂) : r₁ = r₂ := by
  obtain ⟨hw₁, hf₁, h₁⟩ := h₁
  obtain ⟨hw₂, hf₂, h₂⟩ := h₂
  refine Prod.ext ?_ (hf₁.trans hf₂.symm)
  split_ifs at h₁ h₂
  · exact eq_of_isNonNegativeIntegerOf hw₁ hw₂ h₁ h₂
  · exact eq_of_valR_eq fmt hw₁ hw₂ h₁.1 h₂.1 (h₁.2.trans h₂.2.symm) (by rw [h₁.2]; norm_num)

theorem setPayloadResultOf_unique {sp : Specialization} {signaling : Bool} {fmt : Format}
    {x : Nat} {r₁ r₂ : Nat × StatusFlags} (h₁ : setPayloadResultOf sp signaling fmt x r₁)
    (h₂ : setPayloadResultOf sp signaling fmt x r₂) : r₁ = r₂ := by
  obtain ⟨hw₁, hf₁, hn₁, hz₁⟩ := h₁
  obtain ⟨hw₂, hf₂, hn₂, hz₂⟩ := h₂
  refine Prod.ext ?_ (hf₁.trans hf₂.symm)
  by_cases h : ∃ n, IsNonNegativeIntegerOf fmt x n ∧ IsAdmissiblePayload sp fmt signaling n
  · obtain ⟨n, hn, hadm⟩ := h
    obtain ⟨hc₁, hs₁, hp₁⟩ := hn₁ n hn hadm
    obtain ⟨hc₂, hs₂, hp₂⟩ := hn₂ n hn hadm
    have hna : isNaN fmt r₁.1 = true := by unfold isNaN; rw [hc₁]; cases signaling <;> rfl
    exact eq_of_nanPayload_eq hw₁ hw₂ hna (hc₁.trans hc₂.symm) (hs₁.trans hs₂.symm)
      (hp₁.trans hp₂.symm)
  · push Not at h
    exact eq_of_classify_eq_zero fmt hw₁ hw₂ (hz₁ h) (hz₂ h)

theorem setPayloadSpecOf_unique {sp : Specialization} {fmt : Format} {x : Nat}
    {r₁ r₂ : Nat × StatusFlags} (h₁ : SetPayloadSpecOf sp fmt x r₁) (h₂ : SetPayloadSpecOf sp fmt x r₂) :
    r₁ = r₂ :=
  setPayloadResultOf_unique h₁ h₂

theorem setPayloadSignalingSpecOf_unique {sp : Specialization} {fmt : Format} {x : Nat}
    {r₁ r₂ : Nat × StatusFlags} (h₁ : SetPayloadSignalingSpecOf sp fmt x r₁)
    (h₂ : SetPayloadSignalingSpecOf sp fmt x r₂) :
    r₁ = r₂ :=
  setPayloadResultOf_unique h₁ h₂

end SoftFloat.Proof
