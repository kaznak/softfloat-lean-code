/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Round

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem one_le_bias (fmt : Format) : 1 ≤ fmt.bias := by
  have h : 2 ^ 1 ≤ 2 ^ (fmt.expBits - 1) :=
    Nat.pow_le_pow_right (by decide) (by have := fmt.expBits_two_le; omega)
  unfold Format.bias; omega

theorem expMax_eq_two_mul_bias_add_one (fmt : Format) : fmt.expMax = 2 * fmt.bias + 1 := by
  have h : 2 ^ fmt.expBits = 2 * 2 ^ (fmt.expBits - 1) := by
    rw [← pow_succ']; congr 1; have := fmt.expBits_two_le; omega
  have h1 : 1 ≤ 2 ^ (fmt.expBits - 1) := Nat.one_le_two_pow
  unfold Format.expMax Format.bias; omega

theorem minQ_add_fracBits (fmt : Format) : fmt.minQ + fmt.fracBits = emin fmt := by
  unfold Format.minQ emin emax; ring

theorem maxFinite_eq (fmt : Format) :
    maxFinite fmt = ((2 ^ fmt.sigBits - 1 : ℕ) : ℝ) * 2 ^ (emax fmt - fmt.fracBits) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hs := sigBits_eq_fracBits_add_one fmt
  have h1 : 1 ≤ 2 ^ fmt.sigBits := Nat.one_le_two_pow
  have e1 : (2 : ℝ) ^ emax fmt = 2 ^ (fmt.fracBits : ℤ) * 2 ^ (emax fmt - fmt.fracBits) := by
    rw [← zpow_add₀ h2]; ring_nf
  have e2 : (2 : ℝ) ^ (1 - (fmt.sigBits : ℤ)) * 2 ^ emax fmt = 2 ^ (emax fmt - fmt.fracBits) := by
    rw [← zpow_add₀ h2]; congr 1; push_cast [hs]; ring
  unfold maxFinite
  rw [sub_mul, e2, e1, Nat.cast_sub h1, hs, zpow_natCast]
  push_cast; rw [pow_succ]; ring

theorem maxFinite_pos (fmt : Format) : 0 < maxFinite fmt := by
  rw [maxFinite_eq]
  have : 1 < 2 ^ fmt.sigBits := Nat.one_lt_two_pow (by have := fmt.sigBits_two_le; omega)
  have : (0 : ℝ) < ((2 ^ fmt.sigBits - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  positivity

theorem mul_two_zpow_le_maxFinite (fmt : Format) {n : ℕ} (hn : n < 2 ^ fmt.sigBits) {V : ℤ}
    (hV : V + fmt.fracBits ≤ emax fmt) : (n : ℝ) * 2 ^ V ≤ maxFinite fmt := by
  rw [maxFinite_eq]
  have h1 : (n : ℝ) ≤ ((2 ^ fmt.sigBits - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 : (2 : ℝ) ^ V ≤ 2 ^ (emax fmt - fmt.fracBits) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem maxFinite_lt_mul_two_zpow (fmt : Format) {n : ℕ} (hn : 2 ^ fmt.fracBits ≤ n) {V : ℤ}
    (hV : emax fmt + 1 ≤ V + fmt.fracBits) : maxFinite fmt < (n : ℝ) * 2 ^ V := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hlt : maxFinite fmt < 2 ^ (emax fmt + 1) := by
    unfold maxFinite
    have : (0 : ℝ) < 2 ^ (1 - (fmt.sigBits : ℤ)) := by positivity
    rw [zpow_add_one₀ h2]
    have : (0 : ℝ) < 2 ^ emax fmt := by positivity
    nlinarith
  have hn' : ((2 : ℝ) ^ fmt.fracBits) ≤ n := by exact_mod_cast hn
  calc maxFinite fmt < 2 ^ (emax fmt + 1) := hlt
    _ ≤ 2 ^ (V + fmt.fracBits) := zpow_le_zpow_right₀ (by norm_num) hV
    _ = 2 ^ fmt.fracBits * 2 ^ V := by rw [zpow_add₀ h2, zpow_natCast, mul_comm]
    _ ≤ (n : ℝ) * 2 ^ V := mul_le_mul_of_nonneg_right hn' (by positivity)

theorem overflowResult_snd (fmt : Format) (rm : RoundingDirection) (sign : Bool) :
    (fmt.overflowResult rm sign).2 = { overflow := true, inexact := true } := rfl

theorem overflowResult_fst_lt (fmt : Format) (rm : RoundingDirection) (sign : Bool) :
    (fmt.overflowResult rm sign).1 < 2 ^ fmt.width := by
  have h1 := pack_lt fmt sign (expMax_lt fmt) (Nat.two_pow_pos fmt.fracBits)
  have h2 := pack_lt fmt sign (e := fmt.expMax - 1) (by have := expMax_lt fmt; omega)
    (f := 2 ^ fmt.fracBits - 1) (by have := Nat.two_pow_pos fmt.fracBits; omega)
  unfold Format.overflowResult
  cases rm <;> cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption

theorem valR_pack_maxFinite (fmt : Format) (sign : Bool) :
    valR fmt (fmt.pack sign (fmt.expMax - 1) (2 ^ fmt.fracBits - 1)) =
      if sign then -maxFinite fmt else maxFinite fmt := by
  have hb := one_le_bias fmt
  have he := expMax_eq_two_mul_bias_add_one fmt
  have hp := Nat.two_pow_pos fmt.fracBits
  have hs := sigBits_eq_fracBits_add_one fmt
  rw [valR_pack_normal_sig fmt sign (by omega) (by omega) (by omega), maxFinite_eq]
  have h1 : 2 ^ fmt.fracBits + (2 ^ fmt.fracBits - 1) = 2 ^ fmt.sigBits - 1 := by
    rw [hs, pow_succ]; omega
  have h2 : ((fmt.expMax - 1 : ℕ) : ℤ) - (fmt.bias : ℤ) - fmt.fracBits = emax fmt - fmt.fracBits := by
    unfold emax; omega
  rw [h1, h2]
  cases sign
  · simp
  · simp; ring

theorem isFinite_pack_maxFinite (fmt : Format) (sign : Bool) :
    IsFinite fmt (fmt.pack sign (fmt.expMax - 1) (2 ^ fmt.fracBits - 1)) :=
  isFinite_pack fmt sign (by have := expMax_ne_zero fmt; omega)
    (by have := Nat.two_pow_pos fmt.fracBits; omega)

theorem overflowResult_fst_spec (fmt : Format) (rm : RoundingDirection) (sign : Bool) :
    if overflowToInfinity rm sign then classify fmt (fmt.overflowResult rm sign).1 = .infinity sign
    else IsFinite fmt (fmt.overflowResult rm sign).1 ∧
      valR fmt (fmt.overflowResult rm sign).1 = if sign then -maxFinite fmt else maxFinite fmt := by
  have hi := classify_pack_infinity fmt sign
  have hf := isFinite_pack_maxFinite fmt sign
  have hv := valR_pack_maxFinite fmt sign
  unfold Format.overflowResult overflowToInfinity
  cases rm <;> cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Bool.not_true] at hi hf hv ⊢ <;> first | exact hi | exact ⟨hf, hv⟩

theorem abs_sign_mul (sign : Bool) (a : ℝ) (ha : 0 ≤ a) : |(if sign then -1 else 1) * a| = a := by
  cases sign <;> simp [abs_of_nonneg ha]

theorem packBody_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (sign : Bool)
    (x : ℝ) (zn : Bool) (m'' : ℕ) (U' : ℤ) (inexact tiny : Bool)
    (hx0 : x ≠ 0) (hsign : x < 0 ↔ sign = true)
    (hround : roundR fmt rm x = (if sign then -1 else 1) * (m'' : ℝ) * 2 ^ U')
    (hinexact : inexact = true ↔ roundR fmt rm x ≠ x)
    (hU : fmt.minQ ≤ U') (hlt : m'' < 2 ^ fmt.sigBits)
    (hsub : m'' < 2 ^ fmt.fracBits → U' = fmt.minQ ∧ Tiny sp fmt rm x)
    (htiny : 2 ^ fmt.fracBits ≤ m'' → (tiny = true ↔ Tiny sp fmt rm x)) :
    RoundedResultOf sp fmt rm x zn (packBody fmt rm sign m'' U' inexact tiny) := by
  have hb := one_le_bias fmt
  have he := expMax_eq_two_mul_bias_add_one fmt
  have hs := sigBits_eq_fracBits_add_one fmt
  have hN := Nat.two_pow_pos fmt.fracBits
  have h2N : 2 ^ fmt.sigBits = 2 * 2 ^ fmt.fracBits := by rw [hs, pow_succ]; ring
  have habs : |roundR fmt rm x| = (m'' : ℝ) * 2 ^ U' := by
    rw [hround, mul_assoc]; exact abs_sign_mul sign _ (by positivity)
  have hdec : decide (x < 0) = sign := by
    cases sign <;> simp only [Bool.false_eq_true, iff_false, iff_true] at hsign <;> simp [hsign]
  have hfmax : fmt.expMax < 2 ^ fmt.expBits := expMax_lt fmt
  unfold packBody
  dsimp only
  split_ifs with h0 h1 hov
  · -- ゼロに丸める
    subst h0
    have hr0 : roundR fmt rm x = 0 := by rw [hround]; simp
    obtain ⟨-, hT⟩ := hsub hN
    refine ⟨pack_lt fmt sign (by omega) hN, rfl, rfl, ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by rw [hr0, abs_zero]; exact not_lt.mpr (maxFinite_pos fmt).le))]
    refine ⟨isFinite_pack fmt sign (by omega) hN, by rw [valR_pack_zero, hr0], ?_, rfl, ?_, ?_⟩
    · intro _; rw [ite_eq_right_of_eq_false _ _ (eq_false hx0), hdec]; exact classify_pack_zero fmt sign
    · simp only [true_iff, hr0]; exact Ne.symm hx0
    · simp only [true_iff, hr0]; exact ⟨Ne.symm hx0, hT⟩
  · -- 非正規数
    obtain ⟨hUq, hT⟩ := hsub h1
    subst hUq
    have hne : roundR fmt rm x ≠ 0 := by
      rw [← abs_ne_zero, habs]; have : (0 : ℝ) < m'' := by exact_mod_cast Nat.pos_of_ne_zero h0
      positivity
    refine ⟨pack_lt fmt sign (by omega) h1, rfl, rfl, ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr (habs ▸ mul_two_zpow_le_maxFinite fmt hlt
      (by have := minQ_add_fracBits fmt; unfold emin at this; unfold emax at this ⊢; omega))))]
    refine ⟨isFinite_pack fmt sign (by omega) h1, ?_, fun h => absurd h hne, rfl, hinexact, ?_⟩
    · rw [valR_pack_subnormal fmt sign h1, hround]
    · show inexact = true ↔ _
      rw [hinexact]; exact ⟨fun h => ⟨h, hT⟩, fun h => h.1⟩
  · -- 桁あふれ
    have h1' : 2 ^ fmt.fracBits ≤ m'' := by omega
    have hgt : maxFinite fmt < |roundR fmt rm x| := by
      rw [habs]; exact maxFinite_lt_mul_two_zpow fmt h1' (by unfold emax; omega)
    refine ⟨overflowResult_fst_lt fmt rm sign, rfl, rfl, ?_⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hgt), overflowResult_snd, hdec]
    refine ⟨?_, rfl, rfl, rfl⟩
    have hxs : (if x < 0 then -maxFinite fmt else maxFinite fmt) =
        if sign then -maxFinite fmt else maxFinite fmt := by
      cases sign <;> simp only [Bool.false_eq_true, iff_false, iff_true] at hsign <;> simp [hsign]
    rw [hxs]
    exact overflowResult_fst_spec fmt rm sign
  · -- 正規数
    have h1' : 2 ^ fmt.fracBits ≤ m'' := by omega
    have hbe0 : 0 ≤ U' + fmt.fracBits + fmt.bias := by unfold Format.minQ at hU; omega
    have hbeN : (((U' + fmt.fracBits + fmt.bias).toNat : ℕ) : ℤ) = U' + fmt.fracBits + fmt.bias :=
      Int.toNat_of_nonneg hbe0
    have hbe1 : (U' + fmt.fracBits + fmt.bias).toNat ≠ 0 := by unfold Format.minQ at hU; omega
    have hbe2 : (U' + fmt.fracBits + fmt.bias).toNat < fmt.expMax := by omega
    have hf : m'' - 2 ^ fmt.fracBits < 2 ^ fmt.fracBits := by omega
    have hne : roundR fmt rm x ≠ 0 := by
      rw [← abs_ne_zero, habs]; have : (0 : ℝ) < m'' := by exact_mod_cast (by omega : 0 < m'')
      positivity
    refine ⟨pack_lt fmt sign (by omega) hf, rfl, rfl, ?_⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr
      (habs ▸ mul_two_zpow_le_maxFinite fmt hlt (by unfold emax; omega))))]
    refine ⟨isFinite_pack fmt sign hbe2 hf, ?_, fun h => absurd h hne, rfl, hinexact, ?_⟩
    · rw [valR_pack_normal_sig fmt sign hbe1 hbe2 hf, hround, hbeN,
        Nat.add_sub_cancel' h1']
      congr 2; ring
    · show (inexact && tiny) = true ↔ _
      rw [Bool.and_eq_true, hinexact, htiny h1']

end SoftFloat.Proof
