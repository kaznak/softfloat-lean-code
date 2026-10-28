/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.RoundToIntegral
import SoftFloat.Core.Proof.Division
import SoftFloat.Core.Proof.NearestInteger

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem isNearestIntegerTiesToEven_natDiv (X Y : ℕ) (hY : 0 < Y) (up : Prop) [Decidable up]
    (hup : up ↔ Y < X % Y * 2 ∨ (X % Y * 2 = Y ∧ X / Y % 2 = 1)) :
    IsNearestIntegerTiesToEven ((X : ℝ) / Y) ((if up then X / Y + 1 else X / Y : ℕ) : ℤ) := by
  set q0 := X / Y
  set rem := X % Y
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hrem : rem < Y := Nat.mod_lt _ hY
  have hX : (X : ℝ) = Y * q0 + rem := by exact_mod_cast (Nat.div_add_mod X Y).symm
  have hv : (X : ℝ) / Y = q0 + rem / Y := by rw [hX]; field_simp
  set f : ℝ := rem / Y
  have hf0 : 0 ≤ f := by positivity
  have hf1 : f < 1 := (div_lt_one hYR).2 (by exact_mod_cast hrem)
  have hhalf_le : (Y : ℝ) < rem * 2 ↔ 1 / 2 < f := by
    simp only [f]; rw [lt_div_iff₀ hYR]; constructor <;> intro h <;> linarith
  have hhalf_eq : rem * 2 = Y ↔ f = 1 / 2 := by
    simp only [f]; rw [div_eq_iff hYR.ne']
    constructor
    · intro h; have : ((rem * 2 : ℕ) : ℝ) = Y := by exact_mod_cast h
      push_cast at this; linarith
    · intro h; have : ((rem * 2 : ℕ) : ℝ) = Y := by push_cast; linarith
      exact_mod_cast this
  have hmcase : ∀ m : ℤ, (m : ℝ) ≤ q0 ∨ (q0 : ℝ) + 1 ≤ m := by
    intro m
    rcases le_or_gt m (q0 : ℤ) with h | h
    · left; exact_mod_cast h
    · right; have : (q0 : ℤ) + 1 ≤ m := h; exact_mod_cast this
  by_cases hu : up
  · simp only [hu, ↓reduceIte]
    have hge : 1 / 2 ≤ f := by
      rcases hup.1 hu with h | ⟨h, _⟩
      · exact le_of_lt (hhalf_le.1 (by exact_mod_cast h))
      · exact le_of_eq (hhalf_eq.1 h).symm
    have hd : |(((q0 + 1 : ℕ) : ℤ) : ℝ) - X / Y| = 1 - f := by
      rw [hv]; push_cast; rw [abs_of_nonneg (by linarith)]; ring
    refine ⟨fun m => ?_, fun he => ?_⟩
    · rw [hd, hv]
      rcases hmcase m with h | h
      · have := neg_abs_le ((m : ℝ) - (q0 + f)); linarith
      · have := le_abs_self ((m : ℝ) - (q0 + f)); linarith
    · rw [hd] at he
      have hfe : f = 1 / 2 := by linarith
      have hodd : q0 % 2 = 1 := by
        rcases hup.1 hu with h | ⟨_, h⟩
        · exact absurd hfe (ne_of_gt (hhalf_le.1 (by exact_mod_cast h)))
        · exact h
      refine ⟨((q0 + 1 : ℕ) : ℤ) / 2, ?_⟩
      omega
  · simp only [hu, ↓reduceIte]
    have hle : f ≤ 1 / 2 := by
      by_contra h
      rw [not_le] at h
      exact hu (hup.2 (Or.inl (by exact_mod_cast hhalf_le.2 h)))
    have hd : |((q0 : ℕ) : ℤ) - (X : ℝ) / Y| = f := by
      rw [hv]; push_cast; rw [show (q0 : ℝ) - (q0 + f) = -f by ring, abs_neg, abs_of_nonneg hf0]
    refine ⟨fun m => ?_, fun he => ?_⟩
    · rw [hd, hv]
      rcases hmcase m with h | h
      · have := neg_abs_le ((m : ℝ) - (q0 + f)); linarith
      · have := le_abs_self ((m : ℝ) - (q0 + f)); linarith
    · rw [hd] at he
      have heven : q0 % 2 = 0 := by
        by_contra h
        exact hu (hup.2 (Or.inr ⟨hhalf_eq.2 he, by omega⟩))
      refine ⟨(q0 : ℤ) / 2, ?_⟩
      omega

theorem natMod_two_mul_cases (X Y : ℕ) (hY : 0 < Y) :
    (if Y ≤ X % (2 * Y) then X % (2 * Y) - Y else X % (2 * Y)) = X % Y ∧
      (Y ≤ X % (2 * Y) ↔ X / Y % 2 = 1) := by
  have h1 : X % (Y * 2) / Y = X / Y % 2 := Nat.mod_mul_right_div_self X Y 2
  have h2 : X % (Y * 2) % Y = X % Y := Nat.mod_mul_right_mod X Y 2
  have h3 : X % (Y * 2) < Y * 2 := Nat.mod_lt _ (by omega)
  rw [show 2 * Y = Y * 2 by ring]
  set t := X % (Y * 2)
  have hdm := Nat.div_add_mod t Y
  have h4 : X / Y % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.lt_or_ge t Y with h | h
  · have : t / Y = 0 := Nat.div_eq_of_lt h
    have : t % Y = t := Nat.mod_eq_of_lt h
    refine ⟨by simp only [not_le.2 h, ↓reduceIte]; omega, by omega⟩
  · have ht1 : t / Y = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨by simp only [h, ↓reduceIte]; rw [ht1] at hdm; omega, by omega⟩

theorem minQ_le_ulpExpOf (fmt : Format) (u : Unpacked) : fmt.minQ ≤ fmt.ulpExpOf u := by
  unfold Format.ulpExpOf Format.minQ; split_ifs <;> omega

theorem ulpExpOf_add_fracBits_le_emax (fmt : Format) {a : Nat} (hf : IsFinite fmt a) :
    fmt.ulpExpOf (fmt.unpack a) + fmt.fracBits ≤ emax fmt := by
  have hE := expField_lt_expMax_of_isFinite fmt hf
  have h2 := expMax_eq_two_mul_bias_add_one fmt
  have h1 := one_le_bias fmt
  unfold Format.ulpExpOf emax; split_ifs <;> omega

theorem signed_mul_signed_xor (sa sb : Bool) :
    (if sb then (-1 : ℝ) else 1) * (if (sa != sb) then -1 else 1) = if sa then -1 else 1 := by
  cases sa <;> cases sb <;> norm_num

theorem remainder_finite_spec (sp : Specialization) (fmt : Format) {a b : Nat}
    (hfa : IsFinite fmt a) (hfb : IsFinite fmt b) (hzb : isZeroU (fmt.unpack b) = false) :
    (fmt.remainder sp a b).1 < 2 ^ fmt.width ∧ IsFinite fmt (fmt.remainder sp a b).1
    ∧ (∃ n : ℤ, IsNearestIntegerTiesToEven (valR fmt a / valR fmt b) n
        ∧ valR fmt (fmt.remainder sp a b).1 = valR fmt a - valR fmt b * n)
    ∧ (valR fmt (fmt.remainder sp a b).1 = 0 →
        classify fmt (fmt.remainder sp a b).1 = .zero (fmt.unpack a).sign)
    ∧ (fmt.remainder sp a b).2 = {} := by
  set ua := fmt.unpack a with hua
  set ub := fmt.unpack b with hub
  set qa := fmt.ulpExpOf ua
  set qb := fmt.ulpExpOf ub
  set q := min qa qb with hq
  set X := fmt.sigOf ua <<< (qa - q).toNat with hX
  set Y := fmt.sigOf ub <<< (qb - q).toNat with hY
  set t := X % (2 * Y) with ht
  set rem := (if Y ≤ t then t - Y else t) with hrem
  have hmb := sigOf_pos fmt hzb
  have hY0 : 0 < Y := by rw [hY, Nat.shiftLeft_eq]; positivity
  obtain ⟨hremeq, hodd⟩ : rem = X % Y ∧ (Y ≤ t ↔ X / Y % 2 = 1) := natMod_two_mul_cases X Y hY0
  have hremY : rem < Y := hremeq ▸ Nat.mod_lt _ hY0
  have hremX : rem ≤ X := hremeq ▸ Nat.mod_le _ _
  have hXdiv := Nat.div_add_mod X Y
  set q0 := X / Y with hq0
  rw [← hremeq] at hXdiv
  have hqmin : fmt.minQ ≤ q := le_min (minQ_le_ulpExpOf fmt ua) (minQ_le_ulpExpOf fmt ub)
  have hqmax : q + fmt.fracBits ≤ emax fmt := by
    have h1 : qa + fmt.fracBits ≤ emax fmt := ulpExpOf_add_fracBits_le_emax fmt hfa
    have h2 : q ≤ qa := min_le_left qa qb
    omega
  have hsmall : ∀ M, M ≤ X → M ≤ Y → M < 2 ^ fmt.sigBits := by
    intro M h1 h2
    rcases le_total qa qb with h | h
    · have : X = fmt.sigOf ua := by
        rw [hX, show q = qa from min_eq_left h]; simp
      have := sigOf_lt_two_pow_sigBits fmt ua (unpack_fracField_lt fmt a)
      omega
    · have : Y = fmt.sigOf ub := by
        rw [hY, show q = qb from min_eq_right h]; simp
      have := sigOf_lt_two_pow_sigBits fmt ub (unpack_fracField_lt fmt b)
      omega
  have hva : valR fmt a = (if ua.sign then -1 else 1) * (X : ℝ) * 2 ^ q := by
    rw [valR_eq_sigOf fmt hfa, mul_assoc, mul_assoc, hX, shiftLeft_mul_zpow _ (min_le_left _ _)]
  have hvb : valR fmt b = (if ub.sign then -1 else 1) * (Y : ℝ) * 2 ^ q := by
    rw [valR_eq_sigOf fmt hfb, mul_assoc, mul_assoc, hY, shiftLeft_mul_zpow _ (min_le_right _ _)]
  have hpos : (0 : ℝ) < 2 ^ q := by positivity
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY0
  have hdiv : valR fmt a / valR fmt b = (if (ua.sign != ub.sign) then -1 else 1) * ((X : ℝ) / Y) := by
    rw [hva, hvb, ← sign_div_sign]
    field_simp
  set up : Prop := Y < rem * 2 ∨ (rem * 2 = Y ∧ X / Y % 2 = 1) with hup
  have hN := isNearestIntegerTiesToEven_natDiv X Y hY0 up (by rw [hup, ← hremeq])
  have hsig := signed_mul_signed_xor ua.sign ub.sign
  have hXR : (X : ℝ) = Y * ((q0 : ℕ) : ℝ) + rem := by exact_mod_cast hXdiv.symm
  have hdef : fmt.remainder sp a b =
      if (rem * 2 > Y || (rem * 2 == Y && Y ≤ t)) then
        fmt.roundPack sp .roundTiesToEven (!ua.sign) (Y - rem) q
      else if rem = 0 then (fmt.pack ua.sign 0 0, {})
      else fmt.roundPack sp .roundTiesToEven ua.sign rem q := by
    have h1 : fmt.isNaNU ua = false := isNaNU_eq_false_of_isFinite fmt hfa
    have h2 : fmt.isNaNU ub = false := isNaNU_eq_false_of_isFinite fmt hfb
    have h3 : fmt.isInfU ua = false := isInfU_eq_false_of_isFinite fmt hfa
    have h4 : fmt.isInfU ub = false := isInfU_eq_false_of_isFinite fmt hfb
    unfold Format.remainder
    simp only [← hua, ← hub, h1, h2, h3, h4, hzb, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  have hc : (rem * 2 > Y || (rem * 2 == Y && Y ≤ t)) = true ↔ up := by
    rw [hup, ← hodd]; simp [gt_iff_lt]
  rw [hdef]
  by_cases hu : up
  · simp only [hc.2 hu, ↓reduceIte]
    simp only [hu, ↓reduceIte] at hN
    have hge : Y ≤ rem * 2 := by rcases hu with h | ⟨h, _⟩ <;> omega
    have hM0 : 0 < Y - rem := by omega
    obtain ⟨hlt, hfin, hval, hfl⟩ := roundPack_exact_spec sp fmt .roundTiesToEven (!ua.sign) hM0
      (hsmall _ (by omega) (by omega)) hqmin hqmax
    refine ⟨hlt, hfin, ⟨(if (ua.sign != ub.sign) then -1 else 1) * ((q0 + 1 : ℕ) : ℤ), ?_, ?_⟩,
      fun h0 => absurd h0 (hval ▸ signed_ne_zero _ _ _ hM0), hfl⟩
    · rw [hdiv]; exact isNearestIntegerTiesToEven_signed _ hN
    · have hnot : (if (!ua.sign) then (-1 : ℝ) else 1) = -(if ua.sign then -1 else 1) := by
        cases ua.sign <;> norm_num
      rw [hval, hva, hvb, hnot]
      push_cast [Nat.cast_sub hremY.le]
      linear_combination (↑Y * (2 : ℝ) ^ q * (↑q0 + 1)) * hsig
        - ((if ua.sign then (-1 : ℝ) else 1) * 2 ^ q) * hXR
  · have hc' : (rem * 2 > Y || (rem * 2 == Y && Y ≤ t)) = false := by
      cases h : (rem * 2 > Y || (rem * 2 == Y && Y ≤ t))
      · rfl
      · exact absurd (hc.1 h) hu
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    simp only [hu, ↓reduceIte] at hN
    by_cases hr0 : rem = 0
    · simp only [hr0, ↓reduceIte]
      refine ⟨pack_zero_lt _ _, isFinite_pack fmt _ (Nat.pos_of_ne_zero (expMax_ne_zero fmt))
        (by positivity), ⟨(if (ua.sign != ub.sign) then -1 else 1) * ((q0 : ℕ) : ℤ), ?_, ?_⟩,
        fun _ => classify_pack_zero fmt _, trivial⟩
      · rw [hdiv]; exact isNearestIntegerTiesToEven_signed _ hN
      · rw [valR_pack_zero fmt, hva, hvb]
        rw [hr0] at hXR
        push_cast
        linear_combination (↑Y * (2 : ℝ) ^ q * ↑q0) * hsig
          - ((if ua.sign then (-1 : ℝ) else 1) * 2 ^ q) * hXR
    · simp only [hr0, ↓reduceIte]
      have hM0 : 0 < rem := Nat.pos_of_ne_zero hr0
      obtain ⟨hlt, hfin, hval, hfl⟩ := roundPack_exact_spec sp fmt .roundTiesToEven ua.sign hM0
        (hsmall _ hremX hremY.le) hqmin hqmax
      refine ⟨hlt, hfin, ⟨(if (ua.sign != ub.sign) then -1 else 1) * ((q0 : ℕ) : ℤ), ?_, ?_⟩,
        fun h0 => absurd h0 (hval ▸ signed_ne_zero _ _ _ hM0), hfl⟩
      · rw [hdiv]; exact isNearestIntegerTiesToEven_signed _ hN
      · rw [hval, hva, hvb]
        push_cast
        linear_combination (↑Y * (2 : ℝ) ^ q * ↑q0) * hsig
          - ((if ua.sign then (-1 : ℝ) else 1) * 2 ^ q) * hXR

theorem remainderSpecOf_remainder (sp : Specialization) (hsp : Specialization.Valid sp)
    (fmt : Format) {a : Nat} (b : Nat) (ha : a < 2 ^ fmt.width) :
    RemainderSpecOf sp fmt a b (fmt.remainder sp a b) := by
  have hnan := (hsp.propagateNaN .remainder fmt [(fmt, a), (fmt, b)]).2
  unfold RemainderSpecOf
  rw [arithIsInf_eq, arithIsInf_eq, arithIsZero_eq]
  cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b <;>
    simp only [Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rotate_left
  all_goals try
    (simp only [Format.remainder, isNaNU_unpack, isSNaNU_unpack, hna, hnb, Bool.or_true,
      Bool.or_false, ↓reduceIte]; exact ⟨hnan, trivial, trivial⟩)
  cases hia : fmt.isInfU (fmt.unpack a) <;> cases hzb : isZeroU (fmt.unpack b) <;>
    cases hib : fmt.isInfU (fmt.unpack b) <;>
    simp only [Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  all_goals try
    (simp only [Format.remainder, isNaNU_unpack, hna, hnb, hia, hzb, hib, Bool.or_true,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte]
     first
      | exact ⟨hnan, trivial, trivial⟩
      | exact ⟨ha, trivial, trivial⟩)
  have hfa := isFinite_of_not_isNaN_not_isInfU fmt hna hia
  have hfb := isFinite_of_not_isNaN_not_isInfU fmt hnb hib
  obtain ⟨hlt, hfin, hn, hz, hfl⟩ := remainder_finite_spec sp fmt hfa hfb hzb
  rw [arithSign_eq fmt hna]
  exact ⟨hlt, hfin, hn, hz, hfl⟩

theorem softfloat_remainder_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt a b, a < 2 ^ fmt.width → b < 2 ^ fmt.width →
      RemainderSpecOf sp fmt a b ((softfloat sp).remainder fmt a b) :=
  fun fmt _ b ha _ => remainderSpecOf_remainder sp hsp fmt b ha

theorem remainderSpecOf_unique {sp : Specialization} {fmt : Format} {a b : Nat} {r₁ r₂ : Nat × StatusFlags}
    (h₁ : RemainderSpecOf sp fmt a b r₁) (h₂ : RemainderSpecOf sp fmt a b r₂) : r₁ = r₂ := by
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  · obtain ⟨hf₁, ⟨n₁, hn₁, hv₁⟩, hz₁, hfl₁⟩ := h₁
    obtain ⟨hf₂, ⟨n₂, hn₂, hv₂⟩, hz₂, hfl₂⟩ := h₂
    have hv : valR fmt r₁.1 = valR fmt r₂.1 := by
      rw [hv₁, hv₂, isNearestIntegerTiesToEven_unique hn₁ hn₂]
    refine Prod.ext ?_ (hfl₁.trans hfl₂.symm)
    by_cases h0 : valR fmt r₁.1 = 0
    · exact eq_of_classify_eq_zero fmt hw₁ hw₂ (hz₁ h0) (hz₂ (hv ▸ h0))
    · exact eq_of_valR_eq fmt hw₁ hw₂ hf₁ hf₂ hv h0

end SoftFloat.Proof
