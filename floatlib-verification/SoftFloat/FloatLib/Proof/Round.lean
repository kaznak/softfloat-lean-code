/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Real
import SoftFloat.Core.Proof.RoundToOdd

/-!
# The two boundaries of rounding to nearest with ties to even

The rounded value exceeds the largest finite value exactly when the exact value is at least the
midpoint `midR` between the largest finite value and `2 ^ (emax + 1)`. Rounded with an unbounded
exponent range, it is below `2 ^ emin` exactly when the exact value is below the midpoint `umidR`
between `2 ^ emin` and its predecessor on that grid.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof

/-- The midpoint between the largest finite value and `2 ^ (emax + 1)`. -/
noncomputable def midR (fmt : Format) : ℝ :=
  (2 ^ fmt.sigBits - 1 / 2) * 2 ^ (emax fmt + 1 - fmt.sigBits)

/-- The midpoint between `2 ^ emin` and the number below it with `sigBits` significant bits. -/
noncomputable def umidR (fmt : Format) : ℝ :=
  (2 ^ fmt.sigBits - 1 / 2) * 2 ^ (emin fmt - fmt.sigBits)

theorem two_pow_even {k : ℕ} (hk : 1 ≤ k) : ((2 : ℤ) ^ k) % 2 = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hj, pow_succ, Int.mul_emod_left]

theorem two_pow_sigBits_even (fmt : Format) : ((2 : ℤ) ^ fmt.sigBits) % 2 = 0 :=
  two_pow_even (by have := fmt.sigBits_two_le; omega)

/-- Rounding at the scale `2 ^ c` stays below `2 ^ sigBits` units exactly when the value is below
`2 ^ sigBits - 1 / 2` units. -/
theorem rte_mul_lt_iff (fmt : Format) (c : ℤ) (M : ℝ) :
    ((roundMagTiesToEven (M / 2 ^ c) : ℤ) : ℝ) * 2 ^ c < 2 ^ fmt.sigBits * 2 ^ c ↔
      M < (2 ^ fmt.sigBits - 1 / 2) * 2 ^ c := by
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  rw [mul_lt_mul_iff_left₀ hp, ← div_lt_iff₀ hp]
  have h := roundMagTiesToEven_lt_iff (two_pow_sigBits_even fmt) (M / 2 ^ c)
  push_cast at h
  rw [← h]
  constructor
  · intro h1; exact_mod_cast h1
  · intro h1; exact_mod_cast h1

theorem abs_lt_two_zpow_magR (x : ℝ) : |x| < (2 : ℝ) ^ magR x := by
  unfold magR
  exact Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|

theorem magR_eq_of_bounds {x : ℝ} {k : ℤ} (hlo : (2 : ℝ) ^ (k - 1) ≤ |x|) (hhi : |x| < 2 ^ k) :
    magR x = k := by
  have hpos : (0 : ℝ) < |x| := lt_of_lt_of_le (by positivity) hlo
  have h1 := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp (by exact_mod_cast hlo)
  have h2 := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by exact_mod_cast hhi)
  unfold magR
  omega

theorem rte_mul_le_two_pow (fmt : Format) (x : ℝ) {c : ℤ}
    (hc : magR x - fmt.sigBits ≤ c) :
    ((roundMagTiesToEven (|x| / 2 ^ c) : ℤ) : ℝ) * 2 ^ c ≤ 2 ^ ((fmt.sigBits : ℤ) + c) := by
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have hy : |x| / 2 ^ c ≤ ((2 ^ fmt.sigBits : ℤ) : ℝ) := by
    rw [div_le_iff₀ hp]
    push_cast
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    exact (abs_lt_two_zpow_magR x).le.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have h := roundMagTiesToEven_le hy
  rw [zpow_add₀ two_ne_zero, zpow_natCast]
  apply mul_le_mul_of_nonneg_right _ hp.le
  exact_mod_cast h

theorem abs_roundR_rte (fmt : Format) (x : ℝ) :
    |roundR fmt .roundTiesToEven x| =
      ((roundMagTiesToEven (|x| / 2 ^ cexpR fmt x) : ℤ) : ℝ) * 2 ^ cexpR fmt x :=
  abs_roundR_eq fmt .roundTiesToEven x

theorem abs_roundRInf_rte (fmt : Format) (x : ℝ) :
    |roundRInf fmt .roundTiesToEven x| =
      ((roundMagTiesToEven (|x| / 2 ^ cexpRInf fmt x) : ℤ) : ℝ) * 2 ^ cexpRInf fmt x :=
  abs_roundRInf_eq fmt .roundTiesToEven x

theorem emax_sub_sigBits (fmt : Format) : emax fmt - fmt.fracBits = emax fmt + 1 - fmt.sigBits := by
  have := sigBits_eq_fracBits_add_one fmt
  omega

theorem minQ_le_emax_sub (fmt : Format) : fmt.minQ ≤ emax fmt - fmt.sigBits := by
  have := one_le_bias fmt
  have := sigBits_eq_fracBits_add_one fmt
  unfold Format.minQ emax
  omega

theorem midR_pos (fmt : Format) : 0 < midR fmt := by
  unfold midR
  have : (1 : ℝ) ≤ 2 ^ fmt.sigBits := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
  nlinarith

/-- The rounded value exceeds the largest finite value exactly when the exact value is at least
`midR`. -/
theorem maxFinite_lt_abs_roundR_iff (fmt : Format) (x : ℝ) :
    maxFinite fmt < |roundR fmt .roundTiesToEven x| ↔ midR fmt ≤ |x| := by
  by_cases hx : x = 0
  · rw [hx, roundR_zero, abs_zero]
    have := maxFinite_pos fmt
    have := midR_pos fmt
    constructor <;> intro h <;> linarith
  have hp2 := fmt.sigBits_three_le
  have hlo := two_zpow_log_le hx
  have hhi := abs_lt_two_zpow_magR x
  have hmidhi : midR fmt ≤ 2 ^ (emax fmt + 1) := by
    have e : (2 : ℝ) ^ (emax fmt + 1) = 2 ^ fmt.sigBits * 2 ^ (emax fmt + 1 - fmt.sigBits) := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
    unfold midR
    rw [e]
    have : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
    nlinarith
  have hmidlo : (2 : ℝ) ^ emax fmt ≤ midR fmt := by
    have e : (2 : ℝ) ^ emax fmt = 2 ^ (fmt.sigBits - 1) * 2 ^ (emax fmt + 1 - fmt.sigBits) := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; push_cast [show 1 ≤ fmt.sigBits by omega]; ring
    unfold midR
    rw [e]
    have : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
    have h2 : (2 : ℝ) ^ fmt.sigBits = 2 * 2 ^ (fmt.sigBits - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (1 : ℝ) ≤ 2 ^ (fmt.sigBits - 1) := one_le_pow₀ (by norm_num)
    nlinarith
  rcases lt_trichotomy (magR x) (emax fmt + 1) with hk | hk | hk
  · -- Below `2 ^ emax`: the rounded value is at most `2 ^ emax`.
    have hxlt : |x| < 2 ^ emax fmt :=
      hhi.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have hc : cexpR fmt x ≤ emax fmt - fmt.sigBits := by
      have := minQ_le_emax_sub fmt
      unfold cexpR; omega
    have hle := rte_mul_le_two_pow fmt x (c := cexpR fmt x) (by unfold cexpR; omega)
    rw [abs_roundR_rte]
    have : (2 : ℝ) ^ ((fmt.sigBits : ℤ) + cexpR fmt x) ≤ 2 ^ emax fmt :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have := two_zpow_emax_le_maxFinite fmt
    constructor <;> intro h <;> linarith
  · -- In the top binade the rounding is at the scale of the largest finite value.
    have hc : cexpR fmt x = emax fmt + 1 - fmt.sigBits := by
      have := minQ_le_emax_sub fmt
      unfold cexpR; omega
    rw [abs_roundR_rte, hc]
    have hm : maxFinite fmt = ((2 ^ fmt.sigBits - 1 : ℤ) : ℝ) * 2 ^ (emax fmt + 1 - fmt.sigBits) := by
      rw [maxFinite_eq, emax_sub_sigBits]
      have : 1 ≤ 2 ^ fmt.sigBits := Nat.one_le_two_pow
      push_cast [this]
      ring
    have key := rte_mul_lt_iff fmt (emax fmt + 1 - fmt.sigBits) |x|
    unfold midR
    rw [hm, ← not_lt, ← key]
    have hp : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
    rw [mul_lt_mul_iff_left₀ hp, mul_lt_mul_iff_left₀ hp]
    constructor
    · intro h1 h2
      have h1' : (2 : ℤ) ^ fmt.sigBits - 1 < roundMagTiesToEven (|x| / 2 ^ (emax fmt + 1 - fmt.sigBits)) := by
        exact_mod_cast h1
      have h2' : roundMagTiesToEven (|x| / 2 ^ (emax fmt + 1 - fmt.sigBits)) < (2 : ℤ) ^ fmt.sigBits := by
        exact_mod_cast h2
      omega
    · intro h1
      have h1' : ¬ roundMagTiesToEven (|x| / 2 ^ (emax fmt + 1 - fmt.sigBits)) < (2 : ℤ) ^ fmt.sigBits := by
        intro h; exact h1 (by exact_mod_cast h)
      have : (2 : ℤ) ^ fmt.sigBits - 1 < roundMagTiesToEven (|x| / 2 ^ (emax fmt + 1 - fmt.sigBits)) := by
        omega
      exact_mod_cast this
  · -- At or above `2 ^ (emax + 1)`.
    have hge : (2 : ℝ) ^ (emax fmt + 1) ≤ |x| :=
      (zpow_le_zpow_right₀ (by norm_num) (by omega)).trans hlo
    have h1 := two_zpow_le_abs_roundR fmt .roundTiesToEven (k := emax fmt + 1)
      (by have := minQ_le_emax_sub fmt; omega) hge
    have := maxFinite_lt_two_zpow fmt
    constructor <;> intro _ <;> linarith


theorem umidR_lt (fmt : Format) : umidR fmt < 2 ^ emin fmt := by
  have e : (2 : ℝ) ^ emin fmt = 2 ^ fmt.sigBits * 2 ^ (emin fmt - fmt.sigBits) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
  unfold umidR
  rw [e]
  have : (0 : ℝ) < 2 ^ (emin fmt - fmt.sigBits) := by positivity
  nlinarith

theorem le_umidR (fmt : Format) : (2 : ℝ) ^ (emin fmt - 1) ≤ umidR fmt := by
  have hp2 := fmt.sigBits_three_le
  have e : (2 : ℝ) ^ (emin fmt - 1) = 2 ^ (fmt.sigBits - 1) * 2 ^ (emin fmt - fmt.sigBits) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; push_cast [show 1 ≤ fmt.sigBits by omega]; ring
  unfold umidR
  rw [e]
  have : (0 : ℝ) < 2 ^ (emin fmt - fmt.sigBits) := by positivity
  have h2 : (2 : ℝ) ^ fmt.sigBits = 2 * 2 ^ (fmt.sigBits - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : (1 : ℝ) ≤ 2 ^ (fmt.sigBits - 1) := one_le_pow₀ (by norm_num)
  nlinarith

/-- With tininess detected after rounding, a value is tiny exactly when it is nonzero and below
`umidR`. -/
theorem tiny_iff (sp : Specialization) (fmt : Format) (h : sp.tininess = .afterRounding) (x : ℝ) :
    Tiny sp fmt .roundTiesToEven x ↔ x ≠ 0 ∧ |x| < umidR fmt := by
  unfold Tiny
  rw [h]
  refine and_congr_right fun hx => ?_
  have hlo := two_zpow_log_le hx
  have hhi := abs_lt_two_zpow_magR x
  have hu1 := umidR_lt fmt
  have hu2 := le_umidR fmt
  rcases lt_trichotomy (magR x) (emin fmt) with hk | hk | hk
  · have hle := rte_mul_le_two_pow fmt x (c := cexpRInf fmt x) (by unfold cexpRInf; omega)
    rw [abs_roundRInf_rte]
    have h1 : (2 : ℝ) ^ ((fmt.sigBits : ℤ) + cexpRInf fmt x) ≤ 2 ^ (emin fmt - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by unfold cexpRInf; omega)
    have h2 : (2 : ℝ) ^ magR x ≤ 2 ^ (emin fmt - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ (emin fmt - 1) < 2 ^ emin fmt :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    constructor <;> intro _ <;> linarith
  · have hc : cexpRInf fmt x = emin fmt - fmt.sigBits := by unfold cexpRInf; omega
    rw [abs_roundRInf_rte, hc]
    have e : (2 : ℝ) ^ emin fmt = 2 ^ fmt.sigBits * 2 ^ (emin fmt - fmt.sigBits) := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
    rw [e]
    exact rte_mul_lt_iff fmt _ _
  · have hge : (2 : ℝ) ^ emin fmt ≤ |x| :=
      (zpow_le_zpow_right₀ (by norm_num) (by omega)).trans hlo
    have := two_zpow_le_abs_roundRInf fmt .roundTiesToEven hge
    constructor <;> intro _ <;> linarith

/-- A value at least `umidR` rounds to at least `2 ^ emin`. -/
theorem two_zpow_emin_le_abs_roundR (fmt : Format) {x : ℝ} (hx : umidR fmt ≤ |x|) :
    (2 : ℝ) ^ emin fmt ≤ |roundR fmt .roundTiesToEven x| := by
  by_cases hge : (2 : ℝ) ^ emin fmt ≤ |x|
  · exact two_zpow_le_abs_roundR fmt .roundTiesToEven (minQ_le_emin fmt) hge
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hx
    have := le_umidR fmt
    have : (0 : ℝ) < 2 ^ (emin fmt - 1) := by positivity
    linarith
  have hk : magR x = emin fmt := magR_eq_of_bounds ((le_umidR fmt).trans hx) (lt_of_not_ge hge)
  have hs := sigBits_eq_fracBits_add_one fmt
  have hf := one_le_fracBits fmt
  have hmin := minQ_add_fracBits fmt
  have hc : cexpR fmt x = fmt.minQ := by unfold cexpR; omega
  rw [abs_roundR_rte, hc]
  have hp : (0 : ℝ) < 2 ^ fmt.minQ := by positivity
  have e : (2 : ℝ) ^ emin fmt = 2 ^ fmt.fracBits * 2 ^ fmt.minQ := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ← hmin]; ring_nf
  rw [e]
  apply mul_le_mul_of_nonneg_right _ hp.le
  have key := roundMagTiesToEven_lt_iff (two_pow_even hf) (|x| / 2 ^ fmt.minQ)
  have hy : ((2 ^ fmt.fracBits : ℤ) : ℝ) - 1 / 2 ≤ |x| / 2 ^ fmt.minQ := by
    rw [le_div_iff₀ hp]
    have e2 : umidR fmt = (2 ^ fmt.fracBits - 1 / 4) * 2 ^ fmt.minQ := by
      unfold umidR
      rw [show emin fmt - (fmt.sigBits : ℤ) = fmt.minQ - 1 by push_cast [hs]; omega,
        zpow_sub_one₀ two_ne_zero, hs, pow_succ]
      ring
    push_cast
    rw [e2] at hx
    nlinarith
  have : ¬ roundMagTiesToEven (|x| / 2 ^ fmt.minQ) < 2 ^ fmt.fracBits := by
    rw [key]; push_cast at hy ⊢; linarith
  have : (2 : ℤ) ^ fmt.fracBits ≤ roundMagTiesToEven (|x| / 2 ^ fmt.minQ) := by omega
  exact_mod_cast this

end SoftFloat.FloatLib.Proof
