/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Spec

theorem isNearestIntegerTiesToEven_neg {v : ℝ} {n : ℤ} (h : IsNearestIntegerTiesToEven v n) :
    IsNearestIntegerTiesToEven (-v) (-n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m => ?_, fun he => ?_⟩
  · have := h1 (-m)
    push_cast
    rw [show -(n : ℝ) - -v = -((n : ℝ) - v) by ring, abs_neg,
      show (m : ℝ) - -v = -(((-m : ℤ) : ℝ) - v) by push_cast; ring, abs_neg]
    exact this
  · push_cast at he
    rw [show -(n : ℝ) - -v = -((n : ℝ) - v) by ring, abs_neg] at he
    exact (h2 he).neg

theorem isNearestIntegerTiesToEven_signed (s : Bool) {v : ℝ} {n : ℤ}
    (h : IsNearestIntegerTiesToEven v n) :
    IsNearestIntegerTiesToEven ((if s then -1 else 1) * v) ((if s then -1 else 1) * n) := by
  cases s
  · simpa using h
  · simpa using isNearestIntegerTiesToEven_neg h

theorem isNearestIntegerTiesToEven_unique {v : ℝ} {n₁ n₂ : ℤ}
    (h₁ : IsNearestIntegerTiesToEven v n₁) (h₂ : IsNearestIntegerTiesToEven v n₂) : n₁ = n₂ := by
  have he : |(n₁ : ℝ) - v| = |(n₂ : ℝ) - v| := le_antisymm (h₁.1 n₂) (h₂.1 n₁)
  by_contra hne
  have hd : (1 : ℝ) ≤ |(n₁ : ℝ) - n₂| := by
    have : (1 : ℤ) ≤ |n₁ - n₂| := Int.one_le_abs (sub_ne_zero.2 hne)
    exact_mod_cast this
  have htri : |(n₁ : ℝ) - n₂| ≤ |(n₁ : ℝ) - v| + |(n₂ : ℝ) - v| := by
    rw [show (n₁ : ℝ) - n₂ = ((n₁ : ℝ) - v) - ((n₂ : ℝ) - v) by ring]
    exact abs_sub _ _
  have hle : |(n₁ : ℝ) - v| ≤ 1 / 2 := by
    have := h₁.1 (⌊v + 1 / 2⌋)
    have hf1 := Int.floor_le (v + 1 / 2)
    have hf2 := Int.lt_floor_add_one (v + 1 / 2)
    have : |((⌊v + 1 / 2⌋ : ℤ) : ℝ) - v| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hhalf : |(n₁ : ℝ) - v| = 1 / 2 := by linarith
  have e1 := h₁.2 hhalf
  have e2 := h₂.2 (he ▸ hhalf)
  have hd2 : |(n₁ : ℝ) - n₂| ≤ 1 := by linarith
  have hd3 : |n₁ - n₂| = 1 := by
    have : |n₁ - n₂| ≤ 1 := by exact_mod_cast hd2
    have : (1 : ℤ) ≤ |n₁ - n₂| := Int.one_le_abs (sub_ne_zero.2 hne)
    omega
  have hodd : Odd (n₁ - n₂) := by
    rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hd3 with h | h <;> rw [h] <;> decide
  exact (Int.not_even_iff_odd.2 hodd) (e1.sub e2)

end SoftFloat.Proof
