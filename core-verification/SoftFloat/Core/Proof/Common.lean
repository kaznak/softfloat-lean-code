/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Order
import SoftFloat.Core.Proof.RoundPackSpec

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem arithIsInf_eq (fmt : Format) (x : Nat) : arithIsInf fmt x = fmt.isInfU (fmt.unpack x) := by
  cases h : fmt.isInfU (fmt.unpack x)
  · unfold arithIsInf
    split
    · rename_i s hc
      have := ((classify_eq_infinity_iff fmt x s).1 hc).1
      simp_all
    · rfl
  · unfold arithIsInf; rw [(isInfU_unpack_iff fmt x).1 h]

theorem arithIsZero_eq (fmt : Format) (x : Nat) : arithIsZero fmt x = isZeroU (fmt.unpack x) := by
  cases h : isZeroU (fmt.unpack x)
  · unfold arithIsZero
    split
    · rename_i s hc
      have := ((classify_eq_zero_iff fmt x s).1 hc).1
      simp_all
    · rfl
  · unfold arithIsZero; rw [(isZeroU_unpack_iff fmt x).1 h]

theorem arithSign_eq (fmt : Format) {x : Nat} (h : isNaN fmt x = false) :
    arithSign fmt x = (fmt.unpack x).sign := by
  rw [← isNaNU_unpack] at h
  unfold arithSign Format.isNaNU at *
  rw [classify_eq_fields]; dsimp only
  split_ifs <;> simp_all

theorem isFinite_of_not_isNaN_not_isInfU (fmt : Format) {x : Nat} (hn : isNaN fmt x = false)
    (hi : fmt.isInfU (fmt.unpack x) = false) : IsFinite fmt x := by
  rw [isFinite_iff]; exact Nat.ne_of_lt (expField_lt_expMax fmt hn hi)

theorem isZeroU_eq_false_of_isInfU (fmt : Format) {u : Unpacked} (h : fmt.isInfU u = true) :
    isZeroU u = false := by
  cases hz : isZeroU u
  · rfl
  · rw [isInfU_eq_false_of_isZeroU fmt hz] at h; exact absurd h (by decide)

theorem valR_eq_zero_of_isZeroU (fmt : Format) {x : Nat} (h : isZeroU (fmt.unpack x) = true) :
    valR fmt x = 0 :=
  (valR_eq_zero_iff fmt x).2 (Or.inr ⟨_, (isZeroU_unpack_iff fmt x).1 h⟩)

theorem shiftLeft_mul_zpow (m : Nat) {q c : Int} (h : c ≤ q) :
    ((m <<< (q - c).toNat : Nat) : ℝ) * (2 : ℝ) ^ c = (m : ℝ) * (2 : ℝ) ^ q := by
  rw [Nat.shiftLeft_eq]; push_cast
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ two_ne_zero, Int.toNat_of_nonneg (by omega)]
  congr 2; ring

theorem signedShift_mul_zpow (s : Bool) (m : Nat) {q c : Int} (h : c ≤ q) :
    (((if s then -1 else 1) * ((m <<< (q - c).toNat : Nat) : Int) : Int) : ℝ) * (2 : ℝ) ^ c
      = (if s then -1 else 1) * (m : ℝ) * (2 : ℝ) ^ q := by
  rw [mul_assoc, ← shiftLeft_mul_zpow m h]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Int.cast_neg, Int.cast_natCast,
    neg_mul]

theorem alignedSum_mul_zpow (sa sb : Bool) (ma mb : Nat) (qa qb : Int) :
    (((if sa then -1 else 1) * ((ma <<< (qa - min qa qb).toNat : Nat) : Int)
      + (if sb then -1 else 1) * ((mb <<< (qb - min qa qb).toNat : Nat) : Int) : Int) : ℝ)
        * 2 ^ min qa qb
      = (if sa then -1 else 1) * (ma : ℝ) * 2 ^ qa + (if sb then -1 else 1) * (mb : ℝ) * 2 ^ qb := by
  rw [Int.cast_add, add_mul, signedShift_mul_zpow sa ma (min_le_left qa qb),
    signedShift_mul_zpow sb mb (min_le_right qa qb)]

theorem intCast_eq_signed_natAbs (S : ℤ) :
    (S : ℝ) = (if decide (S < 0) then -1 else 1) * ((S.natAbs : ℕ) : ℝ) := by
  rw [Nat.cast_natAbs]
  by_cases h : S < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

theorem signed_mul_signed (sa sb : Bool) (ma mb : Nat) (qa qb : Int) :
    (if sa then -1 else 1) * (ma : ℝ) * 2 ^ qa * ((if sb then -1 else 1) * (mb : ℝ) * 2 ^ qb)
      = (if (sa != sb) then -1 else 1) * ((ma * mb : Nat) : ℝ) * 2 ^ (qa + qb) := by
  rw [zpow_add₀ two_ne_zero]; push_cast
  cases sa <;> cases sb <;> simp <;> ring

theorem valR_mul_valR (fa fb : Format) {a b : Nat} (ha : IsFinite fa a) (hb : IsFinite fb b) :
    valR fa a * valR fb b
      = (if (fa.unpack a).sign != (fb.unpack b).sign then -1 else 1)
        * ((fa.sigOf (fa.unpack a) * fb.sigOf (fb.unpack b) : ℕ) : ℝ)
        * (2 : ℝ) ^ (fa.ulpExpOf (fa.unpack a) + fb.ulpExpOf (fb.unpack b)) := by
  rw [valR_eq_sigOf fa ha, valR_eq_sigOf fb hb, signed_mul_signed]

theorem roundR_zero (fmt : Format) (rm : RoundingDirection) : roundR fmt rm 0 = 0 := by
  unfold roundR; simp [roundAbs_zero]

theorem roundedResultOf_zero (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (zn : Bool) : RoundedResultOf sp fmt rm 0 zn (fmt.pack zn 0 0, {}) := by
  have hpos := maxFinite_pos fmt
  have h0 : (0 : Nat) < fmt.expMax := Nat.pos_of_ne_zero (expMax_ne_zero fmt)
  unfold RoundedResultOf
  rw [roundR_zero, abs_zero]
  simp only [not_lt.mpr hpos.le, ↓reduceIte]
  refine ⟨pack_zero_lt fmt zn, trivial, trivial, isFinite_pack fmt zn h0 (by positivity),
    valR_pack_zero fmt zn, fun _ => classify_pack_zero fmt zn, trivial, by simp, by simp [Tiny]⟩

theorem roundR_signed_exact (fmt : Format) (rm : RoundingDirection) (s : Bool) {m : ℕ} {q : ℤ}
    (hm0 : 0 < m) (hm : m < 2 ^ fmt.sigBits) (hq : fmt.minQ ≤ q) :
    roundR fmt rm ((if s then -1 else 1) * (m : ℝ) * 2 ^ q) = (if s then -1 else 1) * (m : ℝ) * 2 ^ q := by
  rw [roundR_signed fmt rm s m q hm0]
  have hlog : Nat.log2 m ≤ fmt.fracBits := by
    have := (Nat.log2_lt hm0.ne').2 hm
    rw [sigBits_eq_fracBits_add_one] at this
    omega
  have hU : max (topExp m q - fmt.fracBits) fmt.minQ ≤ q := by
    unfold topExp; push_cast; omega
  have hex := (roundAt_mul_eq_iff rm s m q (max (topExp m q - fmt.fracBits) fmt.minQ)).2
    (by simp [inexactAt, hU])
  rw [mul_assoc, hex, mul_assoc]

theorem roundPack_exact_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (s : Bool)
    {m : ℕ} {q : ℤ} (hm0 : 0 < m) (hm : m < 2 ^ fmt.sigBits) (hq : fmt.minQ ≤ q)
    (hq' : q + fmt.fracBits ≤ emax fmt) :
    (fmt.roundPack sp rm s m q).1 < 2 ^ fmt.width ∧ IsFinite fmt (fmt.roundPack sp rm s m q).1 ∧
      valR fmt (fmt.roundPack sp rm s m q).1 = (if s then -1 else 1) * (m : ℝ) * 2 ^ q ∧
      (fmt.roundPack sp rm s m q).2 = {} := by
  have H := roundPack_spec sp fmt rm s m q hm0 s
  have hR := roundR_signed_exact fmt rm s hm0 hm hq
  have hle := mul_two_zpow_le_maxFinite fmt hm hq'
  unfold RoundedResultOf at H
  rw [hR, abs_signed] at H
  simp only [not_lt.mpr hle, ↓reduceIte, ne_eq, not_true_eq_false, false_and, iff_false] at H
  obtain ⟨hlt, hi, hd, hfin, hval, _, ho, hx, hu⟩ := H
  refine ⟨hlt, hfin, hval, ?_⟩
  revert hi hd ho hx hu
  cases (fmt.roundPack sp rm s m q).2
  simp only [Bool.not_eq_true]
  rintro rfl rfl rfl rfl rfl
  rfl

theorem statusFlags_eq {f g : StatusFlags} (h1 : f.inexact = g.inexact)
    (h2 : f.underflow = g.underflow) (h3 : f.overflow = g.overflow)
    (h4 : f.divideByZero = g.divideByZero) (h5 : f.invalidOperation = g.invalidOperation) :
    f = g := by
  cases f; cases g; simp only at h1 h2 h3 h4 h5; subst h1 h2 h3 h4 h5; rfl

theorem bool_eq_of_iff {b c : Bool} {P : Prop} (hb : b = true ↔ P) (hc : c = true ↔ P) : b = c :=
  Bool.eq_iff_iff.2 (hb.trans hc.symm)

theorem expField_eq_of_orderKeyU_eq (fmt : Format) {a b : Nat}
    (h : fmt.orderKeyU (fmt.unpack a) = fmt.orderKeyU (fmt.unpack b)) :
    (fmt.unpack a).expField = (fmt.unpack b).expField := by
  have hM : 0 < 2 ^ fmt.fracBits := by positivity
  have key : ∀ n, fmt.orderKeyU (fmt.unpack n) / 2 ^ fmt.fracBits = (fmt.unpack n).expField := by
    intro n
    unfold Format.orderKeyU
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt (unpack_fracField_lt fmt n),
      Nat.zero_add]
  rw [← key a, ← key b, h]

theorem unpack_eq_of_orderKeyU_eq (fmt : Format) {a b : Nat}
    (hs : (fmt.unpack a).sign = (fmt.unpack b).sign)
    (hk : fmt.orderKeyU (fmt.unpack a) = fmt.orderKeyU (fmt.unpack b)) :
    fmt.unpack a = fmt.unpack b := by
  have he := expField_eq_of_orderKeyU_eq fmt hk
  have hf : (fmt.unpack a).fracField = (fmt.unpack b).fracField := by
    have hfr : ∀ n, fmt.orderKeyU (fmt.unpack n) % 2 ^ fmt.fracBits = (fmt.unpack n).fracField :=
      fun n => by
        unfold Format.orderKeyU
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (unpack_fracField_lt fmt n)]
    rw [← hfr a, ← hfr b, hk]
  cases h : fmt.unpack a; cases h' : fmt.unpack b
  rw [h, h'] at hs he hf
  simp only at hs he hf
  subst hs he hf; rfl

theorem eq_of_sign_eq_of_orderKeyU_eq (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width)
    (hb : b < 2 ^ fmt.width) (hs : (fmt.unpack a).sign = (fmt.unpack b).sign)
    (hk : fmt.orderKeyU (fmt.unpack a) = fmt.orderKeyU (fmt.unpack b)) : a = b :=
  unpack_inj fmt ha hb (unpack_eq_of_orderKeyU_eq fmt hs hk)

theorem orderKeyU_eq_of_magE_eq (fmt : Format) {a b : Nat}
    (ha : isNaN fmt a = false) (hb : isNaN fmt b = false) (h : magE fmt a = magE fmt b) :
    fmt.orderKeyU (fmt.unpack a) = fmt.orderKeyU (fmt.unpack b) := by
  rcases lt_trichotomy (fmt.orderKeyU (fmt.unpack a)) (fmt.orderKeyU (fmt.unpack b))
    with h' | h' | h'
  · exact absurd ((orderKeyU_lt_iff_magE_lt fmt ha hb).1 h') (by rw [h]; exact lt_irrefl _)
  · exact h'
  · exact absurd ((orderKeyU_lt_iff_magE_lt fmt hb ha).1 h') (by rw [h]; exact lt_irrefl _)

theorem eq_of_classify_eq_infinity (fmt : Format) {a b : Nat} {s : Bool}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hca : classify fmt a = .infinity s) (hcb : classify fmt b = .infinity s) : a = b := by
  obtain ⟨hia, hsa⟩ := (classify_eq_infinity_iff fmt a s).1 hca
  obtain ⟨hib, hsb⟩ := (classify_eq_infinity_iff fmt b s).1 hcb
  refine eq_of_sign_eq_of_orderKeyU_eq fmt ha hb (hsa.trans hsb.symm) ?_
  rw [orderKeyU_eq_of_isInfU fmt hia, orderKeyU_eq_of_isInfU fmt hib]

theorem eq_of_classify_eq_zero (fmt : Format) {a b : Nat} {s : Bool}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hca : classify fmt a = .zero s) (hcb : classify fmt b = .zero s) : a = b := by
  obtain ⟨hza, hsa⟩ := (classify_eq_zero_iff fmt a s).1 hca
  obtain ⟨hzb, hsb⟩ := (classify_eq_zero_iff fmt b s).1 hcb
  refine eq_of_sign_eq_of_orderKeyU_eq fmt ha hb (hsa.trans hsb.symm) ?_
  unfold Format.isZeroU at hza hzb
  simp only [Bool.and_eq_true, beq_iff_eq] at hza hzb
  unfold Format.orderKeyU; rw [hza.1, hza.2, hzb.1, hzb.2]

theorem abs_valR_eq_magE (fmt : Format) {n : Nat} (h : IsFinite fmt n) :
    ((|valR fmt n| : ℝ) : EReal) = magE fmt n := by
  rw [magE_of_not_isInfU fmt (isInfU_eq_false_of_isFinite fmt h), valR_eq_sigOf fmt h]
  congr 1
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((fmt.sigOf (fmt.unpack n) : Nat) : ℝ)),
    abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n))]
  split_ifs <;> simp

theorem sign_eq_decide_valR_neg (fmt : Format) {n : Nat} (h : IsFinite fmt n)
    (h0 : valR fmt n ≠ 0) : (fmt.unpack n).sign = decide (valR fmt n < 0) := by
  have hp : (0 : ℝ) ≤ ((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) :=
    by positivity
  have hv : valR fmt n = (if (fmt.unpack n).sign then -1 else 1)
      * (((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n)) := by
    rw [valR_eq_sigOf fmt h, mul_assoc]
  revert h0 hv
  generalize valR fmt n = v
  generalize ((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) = S at hp
  intro h0 hv
  cases hs : (fmt.unpack n).sign <;> rw [hs] at hv <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv
  · exact (decide_eq_false (not_lt.2 (by rw [hv]; linarith))).symm
  · have : v ≤ 0 := by rw [hv]; linarith
    exact (decide_eq_true (lt_of_le_of_ne this h0)).symm

theorem eq_of_valR_eq (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hfa : IsFinite fmt a) (hfb : IsFinite fmt b) (h : valR fmt a = valR fmt b)
    (h0 : valR fmt a ≠ 0) : a = b := by
  have hs : (fmt.unpack a).sign = (fmt.unpack b).sign := by
    rw [sign_eq_decide_valR_neg fmt hfa h0, sign_eq_decide_valR_neg fmt hfb (h ▸ h0), h]
  have hm : magE fmt a = magE fmt b := by
    rw [← abs_valR_eq_magE fmt hfa, ← abs_valR_eq_magE fmt hfb, h]
  exact eq_of_sign_eq_of_orderKeyU_eq fmt ha hb hs
    (orderKeyU_eq_of_magE_eq fmt (isNaN_eq_false_of_isFinite fmt hfa)
      (isNaN_eq_false_of_isFinite fmt hfb) hm)

theorem eq_or_zero_ne_of_valE_eq (fmt : Format) {a b : Nat}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false) (h : valE fmt a = valE fmt b) :
    a = b ∨ ∃ s, classify fmt a = .zero s ∧ classify fmt b = .zero (!s) := by
  by_cases hfa : IsFinite fmt a <;> by_cases hfb : IsFinite fmt b
  · rw [valE_of_isFinite fmt hfa, valE_of_isFinite fmt hfb, EReal.coe_eq_coe_iff] at h
    by_cases h0 : valR fmt a = 0
    · obtain ⟨s, hs⟩ := ((valR_eq_zero_iff fmt a).1 h0).resolve_left (not_not.2 hfa)
      obtain ⟨t, ht⟩ := ((valR_eq_zero_iff fmt b).1 (h ▸ h0)).resolve_left (not_not.2 hfb)
      by_cases hst : s = t
      · subst hst; exact Or.inl (eq_of_classify_eq_zero fmt ha hb hs ht)
      · refine Or.inr ⟨s, hs, ?_⟩
        rw [ht]; cases s <;> cases t <;> simp_all
    · exact Or.inl (eq_of_valR_eq fmt ha hb hfa hfb h h0)
  · obtain ⟨t, ht⟩ := exists_infinity_of_not_isFinite fmt hnb hfb
    rw [valE_of_isFinite fmt hfa] at h
    unfold valE at h; rw [ht] at h
    cases t <;> simp at h
  · obtain ⟨s, hs⟩ := exists_infinity_of_not_isFinite fmt hna hfa
    rw [valE_of_isFinite fmt hfb] at h
    unfold valE at h; rw [hs] at h
    cases s <;> simp at h
  · obtain ⟨s, hs⟩ := exists_infinity_of_not_isFinite fmt hna hfa
    obtain ⟨t, ht⟩ := exists_infinity_of_not_isFinite fmt hnb hfb
    unfold valE at h; rw [hs, ht] at h
    have hst : s = t := by cases s <;> cases t <;> simp_all
    subst hst
    exact Or.inl (eq_of_classify_eq_infinity fmt ha hb hs ht)

theorem roundedResultOf_unique {sp : Specialization} {fmt : Format} {rm : RoundingDirection}
    {x : ℝ} {zn : Bool} {r₁ r₂ : Nat × StatusFlags}
    (h₁ : RoundedResultOf sp fmt rm x zn r₁) (h₂ : RoundedResultOf sp fmt rm x zn r₂) :
    r₁ = r₂ := by
  obtain ⟨hw₁, hi₁, hd₁, h₁⟩ := h₁
  obtain ⟨hw₂, hi₂, hd₂, h₂⟩ := h₂
  by_cases hov : maxFinite fmt < |roundR fmt rm x|
  · simp only [hov, ↓reduceIte] at h₁ h₂
    obtain ⟨h₁, ho₁, hx₁, hu₁⟩ := h₁
    obtain ⟨h₂, ho₂, hx₂, hu₂⟩ := h₂
    have hfl := statusFlags_eq (hx₁.trans hx₂.symm) (hu₁.trans hu₂.symm) (ho₁.trans ho₂.symm)
      (hd₁.trans hd₂.symm) (hi₁.trans hi₂.symm)
    by_cases hinf : overflowToInfinity rm (decide (x < 0)) = true
    · simp only [hinf, ↓reduceIte] at h₁ h₂
      exact Prod.ext (eq_of_classify_eq_infinity fmt hw₁ hw₂ h₁ h₂) hfl
    · simp only [hinf, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      obtain ⟨hf₁, hv₁⟩ := h₁
      obtain ⟨hf₂, hv₂⟩ := h₂
      have hne : valR fmt r₁.1 ≠ 0 := by
        rw [hv₁]; have := maxFinite_pos fmt
        split_ifs
        · exact neg_ne_zero.2 this.ne'
        · exact this.ne'
      exact Prod.ext (eq_of_valR_eq fmt hw₁ hw₂ hf₁ hf₂ (hv₁.trans hv₂.symm) hne) hfl
  · simp only [hov, ↓reduceIte] at h₁ h₂
    obtain ⟨hf₁, hv₁, hz₁, ho₁, hx₁, hu₁⟩ := h₁
    obtain ⟨hf₂, hv₂, hz₂, ho₂, hx₂, hu₂⟩ := h₂
    refine Prod.ext ?_ (statusFlags_eq (bool_eq_of_iff hx₁ hx₂) (bool_eq_of_iff hu₁ hu₂)
      (ho₁.trans ho₂.symm) (hd₁.trans hd₂.symm) (hi₁.trans hi₂.symm))
    by_cases h0 : roundR fmt rm x = 0
    · exact eq_of_classify_eq_zero fmt hw₁ hw₂ (hz₁ h0) (hz₂ h0)
    · exact eq_of_valR_eq fmt hw₁ hw₂ hf₁ hf₂ (hv₁.trans hv₂.symm) (hv₁ ▸ h0)

scoped macro "uniq_close" : tactic => `(tactic| first
  | exact roundedResultOf_unique ‹_› ‹_›
  | (rename_i h₁ h₂; exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm))
  | (rename_i h₁ h₂; exact Prod.ext (eq_of_classify_eq_infinity _ ‹_› ‹_› h₁.1 h₂.1)
      (h₁.2.trans h₂.2.symm))
  | (rename_i h₁ h₂; exact Prod.ext (eq_of_classify_eq_zero _ ‹_› ‹_› h₁.1 h₂.1)
      (h₁.2.trans h₂.2.symm)))

end SoftFloat.Proof
