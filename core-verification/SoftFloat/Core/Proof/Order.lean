/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Encoding

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem compare_eq_compare_of_lt_iff {α β : Type*} [LinearOrder α] [LinearOrder β]
    {x y : α} {x' y' : β} (hlt : x < y ↔ x' < y') (hgt : y < x ↔ y' < x') :
    compare x y = compare x' y' := by
  rcases lt_trichotomy x y with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (hlt.mp h)]
  · subst h
    have h1 : ¬ x' < y' := fun h' => lt_irrefl x (hlt.mpr h')
    have h2 : ¬ y' < x' := fun h' => lt_irrefl x (hgt.mpr h')
    rw [compare_eq_iff_eq.mpr rfl,
      compare_eq_iff_eq.mpr (le_antisymm (not_lt.mp h2) (not_lt.mp h1))]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (hgt.mp h)]

noncomputable def magE (fmt : Format) (n : Nat) : EReal :=
  if fmt.isInfU (fmt.unpack n) then ⊤
  else (((fmt.sigOf (fmt.unpack n) : Nat) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) : ℝ)

theorem magE_of_isInfU (fmt : Format) {n : Nat} (h : fmt.isInfU (fmt.unpack n) = true) :
    magE fmt n = ⊤ := by
  unfold magE; simp only [h, ↓reduceIte]

theorem magE_of_not_isInfU (fmt : Format) {n : Nat} (h : fmt.isInfU (fmt.unpack n) = false) :
    magE fmt n = (((fmt.sigOf (fmt.unpack n) : Nat) : ℝ)
      * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack n) : ℝ) := by
  unfold magE; simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem magE_nonneg (fmt : Format) (n : Nat) : 0 ≤ magE fmt n := by
  unfold magE; split
  · exact le_top
  · exact EReal.coe_nonneg.mpr (by positivity)

theorem isInfU_eq_false_of_isZeroU (fmt : Format) {u : Unpacked} (h : isZeroU u = true) :
    fmt.isInfU u = false := by
  have := expMax_ne_zero fmt
  unfold Format.isZeroU at h; unfold Format.isInfU
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1, Ne.symm this]

theorem isNaNU_eq_false_of_isZeroU (fmt : Format) {u : Unpacked} (h : isZeroU u = true) :
    fmt.isNaNU u = false := by
  have := expMax_ne_zero fmt
  unfold Format.isZeroU at h; unfold Format.isNaNU
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1, Ne.symm this]

theorem isNaN_eq_false_of_isZeroU (fmt : Format) {n : Nat} (h : isZeroU (fmt.unpack n) = true) :
    isNaN fmt n = false := by
  rw [← isNaNU_unpack]; exact isNaNU_eq_false_of_isZeroU fmt h

theorem magE_of_isZeroU (fmt : Format) {n : Nat} (h : isZeroU (fmt.unpack n) = true) :
    magE fmt n = 0 := by
  rw [magE_of_not_isInfU fmt (isInfU_eq_false_of_isZeroU fmt h)]
  unfold Format.isZeroU at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [Format.sigOf, h.1, h.2]

theorem magE_pos (fmt : Format) {n : Nat} (h : isZeroU (fmt.unpack n) = false) :
    0 < magE fmt n := by
  unfold magE; split
  · exact EReal.zero_lt_top
  · exact EReal.coe_pos.mpr (mul_pos (by exact_mod_cast sigOf_pos fmt h) (by positivity))

theorem isSignalingNaN_imp_isNaN (fmt : Format) {n : Nat} (h : isSignalingNaN fmt n = true) :
    isNaN fmt n = true := by
  unfold isSignalingNaN at h; unfold isNaN
  cases hc : classify fmt n <;> simp_all

theorem isSignalingNaN_eq_false_of_isNaN (fmt : Format) {n : Nat} (h : isNaN fmt n = false) :
    isSignalingNaN fmt n = false := by
  cases hs : isSignalingNaN fmt n
  · rfl
  · rw [isSignalingNaN_imp_isNaN fmt hs] at h; simp at h

theorem valE_eq_magE (fmt : Format) {n : Nat} (h : isNaN fmt n = false) :
    valE fmt n = if (fmt.unpack n).sign then -magE fmt n else magE fmt n := by
  by_cases hf : IsFinite fmt n
  · rw [valE_of_isFinite fmt hf, valR_eq_sigOf fmt hf,
      magE_of_not_isInfU fmt (isInfU_eq_false_of_isFinite fmt hf)]
    cases (fmt.unpack n).sign
    · simp
    · simp only [↓reduceIte, ← EReal.coe_neg]; congr 1; ring
  · obtain ⟨s, hs⟩ := exists_infinity_of_not_isFinite fmt h hf
    obtain ⟨hi, hsg⟩ := (classify_eq_infinity_iff fmt n s).1 hs
    unfold valE
    rw [hs, magE_of_isInfU fmt hi, hsg]
    cases s <;> simp

theorem valE_eq_magE_of_nonzero (fmt : Format) {n : Nat} (h : isNaN fmt n = false) :
    valE fmt n = if ((fmt.unpack n).sign && !isZeroU (fmt.unpack n)) then -magE fmt n
      else magE fmt n := by
  rw [valE_eq_magE fmt h]
  cases hz : isZeroU (fmt.unpack n)
  · simp
  · simp [magE_of_isZeroU fmt hz]

theorem valE_of_isZeroU (fmt : Format) {n : Nat} (h : isZeroU (fmt.unpack n) = true) :
    valE fmt n = 0 := by
  rw [valE_eq_magE fmt (isNaN_eq_false_of_isZeroU fmt h), magE_of_isZeroU fmt h]; simp

theorem compare_shiftLeft_eq (x y : Nat) (qa qb : Int) :
    compare (x <<< (qa - Min.min qa qb).toNat) (y <<< (qb - Min.min qa qb).toNat)
      = compare ((x : ℝ) * (2 : ℝ) ^ qa) ((y : ℝ) * (2 : ℝ) ^ qb) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ Min.min qa qb := zpow_pos (by norm_num) _
  have key : ∀ (z : Nat) (p : Int), Min.min qa qb ≤ p →
      (((z <<< (p - Min.min qa qb).toNat : Nat) : ℝ)) * (2 : ℝ) ^ Min.min qa qb
        = (z : ℝ) * (2 : ℝ) ^ p := by
    intro z p hp
    rw [Nat.shiftLeft_eq]; push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), mul_assoc, ← zpow_add₀ (by norm_num)]
    congr 2; ring
  have hx := key x qa (min_le_left _ _)
  have hy := key y qb (min_le_right _ _)
  apply compare_eq_compare_of_lt_iff
  · rw [← hx, ← hy, mul_lt_mul_iff_of_pos_right h2, Nat.cast_lt]
  · rw [← hx, ← hy, mul_lt_mul_iff_of_pos_right h2, Nat.cast_lt]

theorem key_lt_of_exp_lt {P EA EB sA sB : Nat} (hEA : 1 ≤ EA) (hE : EA < EB)
    (hsA : sA < 2 * P) (hsB : P ≤ sB) :
    (EA - 1) * P + sA < (EB - 1) * P + sB ∧ sA * 2 ^ EA < sB * 2 ^ EB := by
  obtain ⟨k, rfl⟩ : ∃ k, EA = k + 1 := ⟨EA - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, EB = k + 1 + 1 + d := ⟨EB - k - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · rw [Nat.add_sub_cancel, show k + 1 + 1 + d - 1 = k + 1 + d by omega]
    nlinarith
  · have hp : 0 < 2 ^ (k + 1) := by positivity
    calc sA * 2 ^ (k + 1) < 2 * P * 2 ^ (k + 1) := Nat.mul_lt_mul_of_pos_right hsA hp
      _ = P * 2 ^ (k + 1 + 1) := by ring
      _ ≤ P * 2 ^ (k + 1 + 1 + d) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ ≤ sB * 2 ^ (k + 1 + 1 + d) := Nat.mul_le_mul_right _ hsB

theorem key_lt_iff_scaled_lt {P EA EB sA sB : Nat} (hEA : 1 ≤ EA) (hEB : 1 ≤ EB)
    (hsA : sA < 2 * P) (hsB : sB < 2 * P) (hA : 2 ≤ EA → P ≤ sA) (hB : 2 ≤ EB → P ≤ sB) :
    (EA - 1) * P + sA < (EB - 1) * P + sB ↔ sA * 2 ^ EA < sB * 2 ^ EB := by
  rcases lt_trichotomy EA EB with h | rfl | h
  · have := key_lt_of_exp_lt hEA h hsA (hB (by omega))
    exact ⟨fun _ => this.2, fun _ => this.1⟩
  · have hp : 0 < 2 ^ EA := by positivity
    rw [Nat.mul_lt_mul_right hp]; omega
  · have := key_lt_of_exp_lt hEB h hsB (hA (by omega))
    constructor
    · intro h'; omega
    · intro h'; omega

theorem expField_lt_expMax (fmt : Format) {n : Nat} (hn : isNaN fmt n = false)
    (hi : fmt.isInfU (fmt.unpack n) = false) : (fmt.unpack n).expField < fmt.expMax := by
  rw [← isNaNU_unpack] at hn
  have h1 := unpack_expField_lt fmt n
  have h2 := expMax_add_one fmt
  unfold Format.isNaNU at hn; unfold Format.isInfU at hi
  by_cases he : (fmt.unpack n).expField = fmt.expMax
  · by_cases hf : (fmt.unpack n).fracField = 0 <;> simp_all
  · omega

theorem orderKeyU_eq_of_isInfU (fmt : Format) {u : Unpacked} (h : fmt.isInfU u = true) :
    fmt.orderKeyU u = fmt.expMax * 2 ^ fmt.fracBits := by
  unfold Format.isInfU at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold Format.orderKeyU; rw [h.1, h.2]; simp

theorem orderKeyU_lt_of_expField_lt (fmt : Format) {u : Unpacked} (he : u.expField < fmt.expMax)
    (hf : u.fracField < 2 ^ fmt.fracBits) : fmt.orderKeyU u < fmt.expMax * 2 ^ fmt.fracBits := by
  unfold Format.orderKeyU
  calc u.expField * 2 ^ fmt.fracBits + u.fracField
      < (u.expField + 1) * 2 ^ fmt.fracBits := by rw [add_mul, one_mul]; omega
    _ ≤ fmt.expMax * 2 ^ fmt.fracBits := Nat.mul_le_mul_right _ he

theorem orderKeyU_eq_sigOf (fmt : Format) (u : Unpacked) :
    fmt.orderKeyU u = ((if u.expField = 0 then 1 else u.expField) - 1) * 2 ^ fmt.fracBits
      + fmt.sigOf u := by
  unfold Format.orderKeyU Format.sigOf
  split_ifs with he
  · simp [he]
  · obtain ⟨k, hk⟩ : ∃ k, u.expField = k + 1 := ⟨u.expField - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]; ring

theorem ulpExpOf_eq (fmt : Format) (u : Unpacked) :
    fmt.ulpExpOf u = (((if u.expField = 0 then 1 else u.expField : Nat)) : Int)
      - ((fmt.bias : Int) + fmt.fracBits) := by
  unfold Format.ulpExpOf; split_ifs <;> push_cast <;> ring

theorem real_mul_zpow_lt_iff (sA sB EA EB : Nat) (c : Int) :
    (sA : ℝ) * (2 : ℝ) ^ ((EA : Int) - c) < (sB : ℝ) * (2 : ℝ) ^ ((EB : Int) - c)
      ↔ sA * 2 ^ EA < sB * 2 ^ EB := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ c := zpow_pos (by norm_num) c
  rw [zpow_sub₀ (by norm_num), zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast,
    ← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff_of_pos_right h2]
  norm_cast

theorem orderKeyU_lt_iff_magE_lt_of_finite (fmt : Format) {a b : Nat}
    (hia : fmt.isInfU (fmt.unpack a) = false) (hib : fmt.isInfU (fmt.unpack b) = false) :
    fmt.orderKeyU (fmt.unpack a) < fmt.orderKeyU (fmt.unpack b) ↔ magE fmt a < magE fmt b := by
  rw [magE_of_not_isInfU fmt hia, magE_of_not_isInfU fmt hib, EReal.coe_lt_coe_iff,
    ulpExpOf_eq, ulpExpOf_eq, real_mul_zpow_lt_iff, orderKeyU_eq_sigOf, orderKeyU_eq_sigOf]
  have hsig : ∀ n, fmt.sigOf (fmt.unpack n) < 2 * 2 ^ fmt.fracBits := by
    intro n; have := unpack_fracField_lt fmt n; unfold Format.sigOf; split_ifs <;> omega
  have hnorm : ∀ n, 2 ≤ (if (fmt.unpack n).expField = 0 then 1 else (fmt.unpack n).expField) →
      2 ^ fmt.fracBits ≤ fmt.sigOf (fmt.unpack n) := by
    intro n h; unfold Format.sigOf; split_ifs at h ⊢ <;> omega
  exact key_lt_iff_scaled_lt (by split_ifs <;> omega) (by split_ifs <;> omega)
    (hsig a) (hsig b) (hnorm a) (hnorm b)

theorem orderKeyU_lt_iff_magE_lt (fmt : Format) {a b : Nat}
    (ha : isNaN fmt a = false) (hb : isNaN fmt b = false) :
    fmt.orderKeyU (fmt.unpack a) < fmt.orderKeyU (fmt.unpack b) ↔ magE fmt a < magE fmt b := by
  cases hia : fmt.isInfU (fmt.unpack a) <;> cases hib : fmt.isInfU (fmt.unpack b)
  · exact orderKeyU_lt_iff_magE_lt_of_finite fmt hia hib
  · rw [orderKeyU_eq_of_isInfU fmt hib, magE_of_isInfU fmt hib, magE_of_not_isInfU fmt hia]
    exact iff_of_true (orderKeyU_lt_of_expField_lt fmt (expField_lt_expMax fmt ha hia)
      (unpack_fracField_lt fmt a)) (EReal.coe_lt_top _)
  · rw [orderKeyU_eq_of_isInfU fmt hia, magE_of_isInfU fmt hia, magE_of_not_isInfU fmt hib]
    exact iff_of_false (Nat.not_lt.mpr (orderKeyU_lt_of_expField_lt fmt
      (expField_lt_expMax fmt hb hib) (unpack_fracField_lt fmt b)).le) (not_lt.mpr le_top)
  · rw [orderKeyU_eq_of_isInfU fmt hia, orderKeyU_eq_of_isInfU fmt hib,
      magE_of_isInfU fmt hia, magE_of_isInfU fmt hib]
    simp

theorem ltU_iff_valE_lt (fmt : Format) {a b : Nat}
    (ha : isNaN fmt a = false) (hb : isNaN fmt b = false)
    (hz : (isZeroU (fmt.unpack a) && isZeroU (fmt.unpack b)) = false) :
    fmt.ltU (fmt.unpack a) (fmt.unpack b) = true ↔ valE fmt a < valE fmt b := by
  rw [valE_eq_magE fmt ha, valE_eq_magE fmt hb]
  have hA := magE_nonneg fmt a
  have hB := magE_nonneg fmt b
  have hkey := orderKeyU_lt_iff_magE_lt fmt ha hb
  have hkey' := orderKeyU_lt_iff_magE_lt fmt hb ha
  unfold Format.ltU
  cases hsa : (fmt.unpack a).sign <;> cases hsb : (fmt.unpack b).sign
  · simpa using hkey
  · simp only [bne_iff_ne, ne_eq, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
      Bool.false_and, false_iff, not_lt]
    have : -magE fmt b ≤ 0 := by simpa using EReal.neg_le_neg_iff.mpr hB
    exact le_trans this hA
  · simp only [hz, bne_iff_ne, ne_eq, Bool.true_eq_false, not_false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.and_self, true_iff]
    rcases Bool.and_eq_false_iff.mp hz with h | h
    · exact lt_of_lt_of_le (by simpa using EReal.neg_lt_neg_iff.mpr (magE_pos fmt h)) hB
    · exact lt_of_le_of_lt (by simpa using EReal.neg_le_neg_iff.mpr hA) (magE_pos fmt h)
  · simpa [EReal.neg_lt_neg_iff] using hkey'

end SoftFloat.Proof
