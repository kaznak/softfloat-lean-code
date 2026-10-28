/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Operators.Round

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem ceil_eq_floor_iff (y : ℝ) : ⌈y⌉ = ⌊y⌋ ↔ y = ⌊y⌋ := by
  constructor
  · intro h
    have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h2 : y ≤ (⌈y⌉ : ℝ) := Int.le_ceil y
    rw [h] at h2; linarith
  · intro h; rw [h, Int.ceil_intCast, Int.floor_intCast]

theorem roundMagToOdd_eq (y : ℝ) :
    roundMagToOdd y = if ⌈y⌉ = ⌊y⌋ then ⌊y⌋ else if ⌊y⌋ % 2 = 0 then ⌊y⌋ + 1 else ⌊y⌋ := by
  have key := ceil_eq_floor_iff y
  unfold roundMagToOdd; dsimp only
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem ceil_le_floor_add_one (y : ℝ) : ⌈y⌉ ≤ ⌊y⌋ + 1 := by
  rw [Int.ceil_le]; push_cast; exact (Int.lt_floor_add_one y).le

theorem floor_le_roundAbs (rm : RoundingDirection) (neg : Bool) (y : ℝ) :
    ⌊y⌋ ≤ roundAbs rm neg y := by
  have hc : ⌊y⌋ ≤ ⌈y⌉ := Int.floor_le_ceil y
  cases rm <;> cases neg <;>
    simp only [roundAbs, roundMagTiesToEven, roundMagTiesToAway, roundMagDown, roundMagUp,
      roundMagToOdd_eq, Bool.false_eq_true, ↓reduceIte] <;> (try split_ifs) <;> omega

theorem roundAbs_le_ceil (rm : RoundingDirection) (neg : Bool) (y : ℝ) :
    roundAbs rm neg y ≤ ⌈y⌉ := by
  have hc : ⌊y⌋ ≤ ⌈y⌉ := Int.floor_le_ceil y
  have hlt : ∀ r : ℝ, 0 < r → r ≤ y - ⌊y⌋ → ⌊y⌋ + 1 ≤ ⌈y⌉ := by
    intro r hr h
    have : ⌊y⌋ < ⌈y⌉ := Int.lt_ceil.mpr (by linarith)
    omega
  have hc1 := ceil_le_floor_add_one y
  cases rm <;> cases neg <;>
    simp only [roundAbs, roundMagTiesToEven, roundMagTiesToAway, roundMagDown, roundMagUp,
      roundMagToOdd_eq, Bool.false_eq_true, ↓reduceIte] <;> (try split_ifs) <;> try omega
  all_goals exact hlt (1 / 2) (by norm_num) (by linarith)

theorem roundAbs_intCast (rm : RoundingDirection) (neg : Bool) (n : ℤ) :
    roundAbs rm neg (n : ℝ) = n := by
  have h1 := floor_le_roundAbs rm neg (n : ℝ)
  have h2 := roundAbs_le_ceil rm neg (n : ℝ)
  simp only [Int.floor_intCast, Int.ceil_intCast] at h1 h2
  omega

theorem roundAbs_natCast (rm : RoundingDirection) (neg : Bool) (n : ℕ) :
    roundAbs rm neg (n : ℝ) = n := by
  simpa using roundAbs_intCast rm neg (n : ℤ)

theorem roundAbs_zero (rm : RoundingDirection) (neg : Bool) : roundAbs rm neg 0 = 0 := by
  simpa using roundAbs_natCast rm neg 0

private theorem div_setup (m d : ℕ) (hd : 0 < d) :
    ⌊(m : ℝ) / d⌋ = ((m / d : ℕ) : ℤ) ∧
      (m : ℝ) / d - ((m / d : ℕ) : ℝ) = ((m % d : ℕ) : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hxeq : (m : ℝ) / d = ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) / d := by
    have hmR : (m : ℝ) = (d : ℝ) * (m / d : ℕ) + (m % d : ℕ) := by
      exact_mod_cast (Nat.div_add_mod m d).symm
    rw [hmR]; field_simp
  have h0 : (0 : ℝ) ≤ ((m % d : ℕ) : ℝ) / d := by positivity
  have h1 : ((m % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdR]; exact_mod_cast Nat.mod_lt m hd
  refine ⟨?_, by rw [hxeq]; ring⟩
  rw [hxeq, Int.floor_natCast_add, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, add_zero]

private theorem ceil_div_eq (m d : ℕ) (hd : 0 < d) :
    ⌈(m : ℝ) / d⌉ = if m % d = 0 then ((m / d : ℕ) : ℤ) else ((m / d : ℕ) : ℤ) + 1 := by
  obtain ⟨hfl, hfr⟩ := div_setup m d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((m % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdR]; exact_mod_cast Nat.mod_lt m hd
  split_ifs with h
  · have : (m : ℝ) / d = ((m / d : ℕ) : ℤ) := by
      rw [h] at hfr; simp only [Nat.cast_zero, zero_div] at hfr
      rw [Int.cast_natCast]; linarith
    rw [this, Int.ceil_intCast]
  · have hpos : (0 : ℝ) < ((m % d : ℕ) : ℝ) / d := by
      have : (0 : ℝ) < ((m % d : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      positivity
    rw [Int.ceil_eq_iff, Int.cast_add, Int.cast_natCast, Int.cast_one]
    constructor <;> linarith

private theorem frac_lt_half_iff (r d : ℕ) (hd : 0 < d) :
    ((r : ℝ) / d < 1 / 2) ↔ r * 2 < d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hdR]
  constructor
  · intro h; have : ((r * 2 : ℕ) : ℝ) < d := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : ((r * 2 : ℕ) : ℝ) < d := by exact_mod_cast h
    push_cast at this; linarith

private theorem half_lt_frac_iff (r d : ℕ) (hd : 0 < d) :
    (1 / 2 < (r : ℝ) / d) ↔ d < r * 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [lt_div_iff₀ hdR]
  constructor
  · intro h; have : (d : ℝ) < ((r * 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : (d : ℝ) < ((r * 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

theorem roundIncr_eq_roundAbs (rm : RoundingDirection) (neg : Bool) (m d : ℕ) (hd : 0 < d) :
    ((if roundIncr rm neg (m / d) (m % d) d then m / d + 1 else m / d : ℕ) : ℤ)
      = roundAbs rm neg ((m : ℝ) / d) := by
  obtain ⟨hfl, hfr⟩ := div_setup m d hd
  have hce := ceil_div_eq m d hd
  have hlt := frac_lt_half_iff (m % d) d hd
  have hgt := half_lt_frac_iff (m % d) d hd
  have hle : (1 / 2 ≤ ((m % d : ℕ) : ℝ) / d) ↔ d ≤ m % d * 2 := by
    rw [← not_lt, hlt]; omega
  cases rm
  case roundToOdd =>
    simp only [roundIncr, roundAbs, roundMagToOdd_eq, hfl, hce, Bool.and_eq_true, bne_iff_ne,
      ne_eq, beq_iff_eq]
    split_ifs <;> push_cast <;> omega
  all_goals cases neg <;>
    simp only [roundIncr, roundAbs, roundMagTiesToEven, roundMagTiesToAway, roundMagDown,
      roundMagUp, hfl, hce, Int.cast_natCast, hfr, hlt, hgt, hle, Bool.false_eq_true, ↓reduceIte,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, bne_iff_ne, ne_eq,
      ge_iff_le, gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] <;>
    (try split_ifs) <;> (try simp only [Nat.cast_add, Nat.cast_one] at *) <;> omega

theorem ceil_sub_half_le_roundMagTiesToEven (y : ℝ) : ⌈y - 1 / 2⌉ ≤ roundMagTiesToEven y := by
  have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  unfold roundMagTiesToEven; dsimp only
  split_ifs <;> rw [Int.ceil_le] <;> push_cast <;> linarith

theorem roundMagTiesToEven_le_floor_add_half (y : ℝ) : roundMagTiesToEven y ≤ ⌊y + 1 / 2⌋ := by
  have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  unfold roundMagTiesToEven; dsimp only
  split_ifs <;> rw [Int.le_floor] <;> push_cast <;> linarith

theorem ceil_sub_half_le_roundMagTiesToAway (y : ℝ) : ⌈y - 1 / 2⌉ ≤ roundMagTiesToAway y := by
  have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  unfold roundMagTiesToAway; dsimp only
  split_ifs <;> rw [Int.ceil_le] <;> push_cast <;> linarith

theorem roundMagTiesToAway_le_floor_add_half (y : ℝ) : roundMagTiesToAway y ≤ ⌊y + 1 / 2⌋ := by
  have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h2 : y < ⌊y⌋ + 1 := Int.lt_floor_add_one y
  unfold roundMagTiesToAway; dsimp only
  split_ifs <;> rw [Int.le_floor] <;> push_cast <;> linarith

theorem le_roundAbs_half (rm : RoundingDirection) (neg : Bool) (y : ℝ) (N : ℤ)
    (hy : y < 2 * N) (h : roundAbs rm neg y = 2 * N) : N ≤ roundAbs rm neg (y / 2) := by
  have hfl : ⌊y⌋ < 2 * N := Int.floor_lt.mpr (by push_cast; exact hy)
  have hce : 2 * N ≤ ⌈y⌉ := h ▸ roundAbs_le_ceil rm neg y
  have hy1 : ((2 * N : ℤ) : ℝ) - 1 < y := Int.le_ceil_iff.mp hce
  push_cast at hy1
  have hc2 : N ≤ ⌈y / 2⌉ := Int.le_ceil_iff.mpr (by linarith)
  have hc1 := ceil_le_floor_add_one y
  cases rm <;> cases neg <;>
    simp only [roundAbs, roundMagDown, roundMagUp, roundMagToOdd_eq, Bool.false_eq_true,
      ↓reduceIte] at h ⊢ <;>
    (try split_ifs at h) <;>
    first
      | omega
      | (have h3 := roundMagTiesToEven_le_floor_add_half y
         have h4 := ceil_sub_half_le_roundMagTiesToEven (y / 2)
         have h5 : (2 * N : ℝ) ≤ y + 1 / 2 := by
           have := Int.le_floor.mp (h ▸ h3); push_cast at this; exact this
         have h6 : N ≤ ⌈y / 2 - 1 / 2⌉ := Int.le_ceil_iff.mpr (by linarith)
         omega)
      | (have h3 := roundMagTiesToAway_le_floor_add_half y
         have h4 := ceil_sub_half_le_roundMagTiesToAway (y / 2)
         have h5 : (2 * N : ℝ) ≤ y + 1 / 2 := by
           have := Int.le_floor.mp (h ▸ h3); push_cast at this; exact this
         have h6 : N ≤ ⌈y / 2 - 1 / 2⌉ := Int.le_ceil_iff.mpr (by linarith)
         omega)

end SoftFloat.Proof
