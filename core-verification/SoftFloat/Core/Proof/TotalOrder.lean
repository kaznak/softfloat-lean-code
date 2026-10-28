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

theorem nan_fields (fmt : Format) {n : Nat} (h : isNaN fmt n = true) :
    (fmt.unpack n).expField = fmt.expMax ∧ (fmt.unpack n).fracField ≠ 0 := by
  rw [← isNaNU_unpack] at h
  unfold Format.isNaNU at h
  simpa using h

theorem orderKeyU_lt_of_isNaN (fmt : Format) {a b : Nat} (ha : isNaN fmt a = true)
    (hb : isNaN fmt b = false) : fmt.orderKeyU (fmt.unpack b) < fmt.orderKeyU (fmt.unpack a) := by
  obtain ⟨hea, hfa⟩ := nan_fields fmt ha
  have hka : fmt.orderKeyU (fmt.unpack a) = fmt.expMax * 2 ^ fmt.fracBits
      + (fmt.unpack a).fracField := by
    unfold Format.orderKeyU; rw [hea]
  rw [hka]
  cases hib : fmt.isInfU (fmt.unpack b)
  · have := orderKeyU_lt_of_expField_lt fmt (expField_lt_expMax fmt hb hib)
      (unpack_fracField_lt fmt b)
    omega
  · rw [orderKeyU_eq_of_isInfU fmt hib]; omega

theorem classify_of_isNaN (fmt : Format) {n : Nat} (h : isNaN fmt n = true) :
    classify fmt n = if fmt.quietBit ≤ (fmt.unpack n).fracField then .quietNaN
      else .signalingNaN := by
  obtain ⟨he, hf⟩ := nan_fields fmt h
  rw [classify_eq_fields]
  simp [he, hf]

theorem orderKeyU_le_iff_of_isNaN (fmt : Format) {a b : Nat} (ha : isNaN fmt a = true)
    (hb : isNaN fmt b = true) :
    fmt.orderKeyU (fmt.unpack a) ≤ fmt.orderKeyU (fmt.unpack b)
      ↔ (fmt.unpack a).fracField ≤ (fmt.unpack b).fracField := by
  unfold Format.orderKeyU
  rw [(nan_fields fmt ha).1, (nan_fields fmt hb).1]
  omega

theorem nanPayload_le_iff (fmt : Format) {a b : Nat}
    (hq : fmt.quietBit ≤ (fmt.unpack a).fracField ↔ fmt.quietBit ≤ (fmt.unpack b).fracField) :
    nanPayload fmt a ≤ nanPayload fmt b ↔ (fmt.unpack a).fracField ≤ (fmt.unpack b).fracField := by
  have h2 := two_pow_fracBits_eq fmt
  have hqa := unpack_fracField_lt fmt a
  have hqb := unpack_fracField_lt fmt b
  have hpay : ∀ n, nanPayload fmt n = if fmt.quietBit ≤ (fmt.unpack n).fracField
      then (fmt.unpack n).fracField - fmt.quietBit else (fmt.unpack n).fracField := by
    intro n
    have := unpack_fracField_lt fmt n
    unfold nanPayload
    change (fmt.unpack n).fracField % fmt.quietBit = _
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hpay a, hpay b]
  by_cases h : fmt.quietBit ≤ (fmt.unpack a).fracField
  · have h' : fmt.quietBit ≤ (fmt.unpack b).fracField := by exact hq.1 h
    simp only [h, h', ↓reduceIte]; omega
  · have h' : ¬ fmt.quietBit ≤ (fmt.unpack b).fracField := by exact fun h'' => h (hq.2 h'')
    simp only [h, h', ↓reduceIte]

def totalOrderByKeys (fmt : Format) (a b : Nat) : Bool :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if ua.sign != ub.sign then ua.sign
  else if ua.sign then decide (fmt.orderKeyU ub ≤ fmt.orderKeyU ua)
  else decide (fmt.orderKeyU ua ≤ fmt.orderKeyU ub)

theorem totalOrder_eq_byKeys (sp : Specialization) (fmt : Format) {a b : Nat}
    (h : (fmt.unpack a).sign = (fmt.unpack b).sign →
      (fmt.isNaNU (fmt.unpack a) && fmt.isNaNU (fmt.unpack b)
        && fmt.isSNaNU (fmt.unpack a) == fmt.isSNaNU (fmt.unpack b)) = false) :
    fmt.totalOrder sp a b = totalOrderByKeys fmt a b := by
  unfold Format.totalOrder totalOrderByKeys
  dsimp only
  by_cases hs : (fmt.unpack a).sign = (fmt.unpack b).sign
  · rw [h hs]; simp only [Bool.false_eq_true, ↓reduceIte]
  · have hs' : ((fmt.unpack a).sign != (fmt.unpack b).sign) = true := by simpa using hs
    simp only [hs', ↓reduceIte]

theorem totalOrder_eq_byKeys_of_isNaN_false (sp : Specialization) (fmt : Format) {a b : Nat}
    (h : isNaN fmt a = false ∨ isNaN fmt b = false) :
    fmt.totalOrder sp a b = totalOrderByKeys fmt a b := by
  refine totalOrder_eq_byKeys sp fmt fun _ => ?_
  rcases h with h | h <;> simp [isNaNU_unpack, h]

theorem not_both_zero_of_valE_lt (fmt : Format) {a b : Nat} (h : valE fmt a < valE fmt b) :
    (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false := by
  cases ha : isZeroU (fmt.unpack a) <;> cases hb : isZeroU (fmt.unpack b) <;> try rfl
  rw [valE_of_isZeroU fmt ha, valE_of_isZeroU fmt hb] at h
  exact absurd h (lt_irrefl _)

theorem totalOrder_of_valE_lt (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) (h : valE fmt a < valE fmt b) : totalOrderByKeys fmt a b = true := by
  have hl := (ltU_iff_valE_lt fmt ha hb (not_both_zero_of_valE_lt fmt h)).2 h
  unfold Format.ltU at hl
  unfold totalOrderByKeys; dsimp only
  cases hsa : (fmt.unpack a).sign <;> cases hsb : (fmt.unpack b).sign <;>
    simp_all <;> omega

theorem totalOrder_of_valE_gt (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) (h : valE fmt b < valE fmt a) : totalOrderByKeys fmt a b = false := by
  have hl := (ltU_iff_valE_lt fmt hb ha (not_both_zero_of_valE_lt fmt h)).2 h
  unfold Format.ltU at hl
  unfold totalOrderByKeys; dsimp only
  cases hsa : (fmt.unpack a).sign <;> cases hsb : (fmt.unpack b).sign <;>
    simp_all

theorem orderKeyU_eq_of_valE_eq (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) (hs : (fmt.unpack a).sign = (fmt.unpack b).sign)
    (h : valE fmt a = valE fmt b) :
    fmt.orderKeyU (fmt.unpack a) = fmt.orderKeyU (fmt.unpack b) := by
  by_cases hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = true
  · simp only [Bool.and_eq_true] at hz
    unfold Format.isZeroU at hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hz
    unfold Format.orderKeyU; rw [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  · have hz' : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false := by simpa using hz
    have hz'' : (isZeroU (fmt.unpack b) && isZeroU (fmt.unpack a)) = false := by
      rw [Bool.and_comm]; exact hz'
    have h1 : fmt.ltU (fmt.unpack a) (fmt.unpack b) = false := by
      cases hl : fmt.ltU (fmt.unpack a) (fmt.unpack b)
      · rfl
      · exact absurd ((ltU_iff_valE_lt fmt ha hb hz').1 hl) (by rw [h]; exact lt_irrefl _)
    have h2 : fmt.ltU (fmt.unpack b) (fmt.unpack a) = false := by
      cases hl : fmt.ltU (fmt.unpack b) (fmt.unpack a)
      · rfl
      · exact absurd ((ltU_iff_valE_lt fmt hb ha hz'').1 hl) (by rw [h]; exact lt_irrefl _)
    unfold Format.ltU at h1 h2
    cases hsa : (fmt.unpack a).sign <;> rw [hsa] at hs <;> rw [hsa, ← hs] at h1 h2 <;>
      simp at h1 h2 <;> omega

theorem totalOrderSpecOf_totalOrder (sp : Specialization) (fmt : Format) (x y : Nat) :
    TotalOrderSpecOf sp fmt x y (fmt.totalOrder sp x y) := by
  unfold TotalOrderSpecOf
  dsimp only
  by_cases hn : isNaN fmt x = false ∧ isNaN fmt y = false
  · simp only [hn, and_self, ↓reduceIte]
    obtain ⟨hx, hy⟩ := hn
    rw [totalOrder_eq_byKeys_of_isNaN_false sp fmt (Or.inl hx)]
    refine ⟨totalOrder_of_valE_lt fmt hx hy, totalOrder_of_valE_gt fmt hx hy, fun he => ⟨?_, ?_, ?_⟩⟩
    · intro h1 h2
      unfold totalOrderByKeys; dsimp only
      simp [((classify_eq_zero_iff fmt x true).1 h1).2, ((classify_eq_zero_iff fmt y false).1 h2).2]
    · intro h1 h2
      unfold totalOrderByKeys; dsimp only
      simp [((classify_eq_zero_iff fmt x false).1 h1).2, ((classify_eq_zero_iff fmt y true).1 h2).2]
    · intro hs
      have hk := orderKeyU_eq_of_valE_eq fmt hx hy hs he
      have hq : fmt.ulpExpOf (fmt.unpack x) = fmt.ulpExpOf (fmt.unpack y) := by
        unfold Format.ulpExpOf; rw [expField_eq_of_orderKeyU_eq fmt hk]
      unfold totalOrderByKeys; dsimp only
      simp only [hs, hk, hq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, le_refl,
        decide_true, ite_self]
  · simp only [hn, ↓reduceIte]
    cases hx : isNaN fmt x <;> cases hy : isNaN fmt y
    · simp [hx, hy] at hn
    · simp only [Bool.true_eq_false, ↓reduceIte]
      have hk := orderKeyU_lt_of_isNaN fmt hy hx
      rw [totalOrder_eq_byKeys_of_isNaN_false sp fmt (Or.inl hx)]
      unfold totalOrderByKeys; dsimp only
      cases hsa : (fmt.unpack x).sign <;> cases hsb : (fmt.unpack y).sign <;> simp <;> omega
    · simp only [↓reduceIte]
      have hk := orderKeyU_lt_of_isNaN fmt hx hy
      rw [totalOrder_eq_byKeys_of_isNaN_false sp fmt (Or.inr hy)]
      unfold totalOrderByKeys; dsimp only
      cases hsa : (fmt.unpack x).sign <;> cases hsb : (fmt.unpack y).sign <;> simp <;> omega
    · simp only [Bool.true_eq_false, ↓reduceIte]
      have hle := orderKeyU_le_iff_of_isNaN fmt hx hy
      have hle' := orderKeyU_le_iff_of_isNaN fmt hy hx
      have hsx := isSNaNU_unpack fmt x
      have hsy := isSNaNU_unpack fmt y
      rw [isSignalingNaN_eq_decide, classify_of_isNaN fmt hx] at hsx
      rw [isSignalingNaN_eq_decide, classify_of_isNaN fmt hy] at hsy
      rw [classify_of_isNaN fmt hx, classify_of_isNaN fmt hy]
      by_cases hs : (fmt.unpack x).sign = (fmt.unpack y).sign
      · by_cases hk : (fmt.quietBit ≤ (fmt.unpack x).fracField ↔ fmt.quietBit ≤ (fmt.unpack y).fracField)
        · have hc : (fmt.isNaNU (fmt.unpack x) && fmt.isNaNU (fmt.unpack y)
              && fmt.isSNaNU (fmt.unpack x) == fmt.isSNaNU (fmt.unpack y)) = true := by
            rw [isNaNU_unpack, isNaNU_unpack, hx, hy, hsx, hsy]
            by_cases hqx : fmt.quietBit ≤ (fmt.unpack x).fracField <;>
              by_cases hqy : fmt.quietBit ≤ (fmt.unpack y).fracField <;> simp_all
          have ht : fmt.totalOrder sp x y = sp.totalOrderNaN fmt x y := by
            unfold Format.totalOrder; dsimp only
            have hs' : ((fmt.unpack x).sign != (fmt.unpack y).sign) = false := by simpa using hs
            simp only [hs', hc, Bool.false_eq_true, ↓reduceIte]
          rw [ht]
          by_cases hqx : fmt.quietBit ≤ (fmt.unpack x).fracField <;>
            by_cases hqy : fmt.quietBit ≤ (fmt.unpack y).fracField <;> simp_all
        · have hc : (fmt.isNaNU (fmt.unpack x) && fmt.isNaNU (fmt.unpack y)
              && fmt.isSNaNU (fmt.unpack x) == fmt.isSNaNU (fmt.unpack y)) = false := by
            rw [isNaNU_unpack, isNaNU_unpack, hx, hy, hsx, hsy]
            by_cases hqx : fmt.quietBit ≤ (fmt.unpack x).fracField <;>
              by_cases hqy : fmt.quietBit ≤ (fmt.unpack y).fracField <;> simp_all
          rw [totalOrder_eq_byKeys sp fmt fun _ => hc]
          unfold totalOrderByKeys; dsimp only
          cases hsx' : (fmt.unpack x).sign <;> rw [hsx'] at hs <;> rw [← hs] <;>
            by_cases hqx : fmt.quietBit ≤ (fmt.unpack x).fracField <;>
            by_cases hqy : fmt.quietBit ≤ (fmt.unpack y).fracField <;>
            simp_all <;> omega
      · rw [totalOrder_eq_byKeys sp fmt fun h => absurd h hs]
        unfold totalOrderByKeys; dsimp only
        cases hsa : (fmt.unpack x).sign <;> cases hsb : (fmt.unpack y).sign <;> simp_all

theorem totalOrderMagSpecOf_totalOrderMag (sp : Specialization) (fmt : Format) {x y : Nat}
    (hx : x < 2 ^ fmt.width) (hy : y < 2 ^ fmt.width) :
    TotalOrderMagSpecOf sp fmt x y (fmt.totalOrderMag sp x y) := by
  unfold TotalOrderMagSpecOf Format.totalOrderMag Format.abs
  rw [clearSign_eq_withSign fmt hx, clearSign_eq_withSign fmt hy]
  exact totalOrderSpecOf_totalOrder sp fmt _ _

theorem softfloat_totalOrder_spec (sp : Specialization) :
    ∀ fmt x y, x < 2 ^ fmt.width → y < 2 ^ fmt.width →
      TotalOrderSpecOf sp fmt x y ((softfloat sp).totalOrder fmt x y) :=
  fun fmt x y _ _ => totalOrderSpecOf_totalOrder sp fmt x y

theorem softfloat_totalOrderMag_spec (sp : Specialization) :
    ∀ fmt x y, x < 2 ^ fmt.width → y < 2 ^ fmt.width →
      TotalOrderMagSpecOf sp fmt x y ((softfloat sp).totalOrderMag fmt x y) :=
  fun fmt _ _ hx hy => totalOrderMagSpecOf_totalOrderMag sp fmt hx hy

theorem isZeroU_of_valE_eq_of_sign_ne (fmt : Format) {a b : Nat} (ha : isNaN fmt a = false)
    (hb : isNaN fmt b = false) (hs : (fmt.unpack a).sign ≠ (fmt.unpack b).sign)
    (h : valE fmt a = valE fmt b) :
    isZeroU (fmt.unpack a) = true ∧ isZeroU (fmt.unpack b) = true := by
  by_contra hz
  have hz' : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false := by
    simpa [Bool.and_eq_true] using hz
  have hz'' : (isZeroU (fmt.unpack b) && isZeroU (fmt.unpack a)) = false := by
    rw [Bool.and_comm]; exact hz'
  have h1 := ltU_iff_valE_lt fmt ha hb hz'
  have h2 := ltU_iff_valE_lt fmt hb ha hz''
  rw [h, iff_false_intro (lt_irrefl _)] at h1 h2
  unfold Format.ltU at h1 h2
  cases hsa : (fmt.unpack a).sign <;> cases hsb : (fmt.unpack b).sign <;>
    simp [hsa, hsb, hz', hz''] at hs h1 h2

theorem totalOrderSpecOf_unique {sp : Specialization} {fmt : Format} {x y : Nat} {r₁ r₂ : Bool}
    (h₁ : TotalOrderSpecOf sp fmt x y r₁) (h₂ : TotalOrderSpecOf sp fmt x y r₂) : r₁ = r₂ := by
  unfold TotalOrderSpecOf at h₁ h₂
  dsimp only at h₁ h₂
  by_cases hn : isNaN fmt x = false ∧ isNaN fmt y = false
  · simp only [hn, and_self, ↓reduceIte] at h₁ h₂
    obtain ⟨hx, hy⟩ := hn
    rcases lt_trichotomy (valE fmt x) (valE fmt y) with h | h | h
    · exact (h₁.1 h).trans (h₂.1 h).symm
    · obtain ⟨c1, c2, c3⟩ := h₁.2.2 h
      obtain ⟨d1, d2, d3⟩ := h₂.2.2 h
      by_cases hs : (fmt.unpack x).sign = (fmt.unpack y).sign
      · exact Bool.eq_iff_iff.2 ((c3 hs).trans (d3 hs).symm)
      · obtain ⟨zx, zy⟩ := isZeroU_of_valE_eq_of_sign_ne fmt hx hy hs h
        cases hsx : (fmt.unpack x).sign <;> cases hsy : (fmt.unpack y).sign <;> rw [hsx, hsy] at hs
        · exact absurd rfl hs
        · have ex := (classify_eq_zero_iff fmt x false).2 ⟨zx, hsx⟩
          have ey := (classify_eq_zero_iff fmt y true).2 ⟨zy, hsy⟩
          exact (c2 ex ey).trans (d2 ex ey).symm
        · have ex := (classify_eq_zero_iff fmt x true).2 ⟨zx, hsx⟩
          have ey := (classify_eq_zero_iff fmt y false).2 ⟨zy, hsy⟩
          exact (c1 ex ey).trans (d1 ex ey).symm
        · exact absurd rfl hs
    · exact (h₁.2.1 h).trans (h₂.2.1 h).symm
  · simp only [hn, ↓reduceIte] at h₁ h₂
    split_ifs at h₁ h₂ <;> exact h₁.trans h₂.symm

theorem totalOrderMagSpecOf_unique {sp : Specialization} {fmt : Format} {x y : Nat} {r₁ r₂ : Bool}
    (h₁ : TotalOrderMagSpecOf sp fmt x y r₁) (h₂ : TotalOrderMagSpecOf sp fmt x y r₂) : r₁ = r₂ :=
  totalOrderSpecOf_unique h₁ h₂

