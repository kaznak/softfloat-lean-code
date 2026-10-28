/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.RoundR

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

def roundAt (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) : ℕ :=
  if U ≤ q then m <<< (q - U).toNat
  else
    let d := 2 ^ (U - q).toNat
    if roundIncr rm sign (m / d) (m % d) d then m / d + 1 else m / d

def inexactAt (m : ℕ) (q U : ℤ) : Bool :=
  if U ≤ q then false else m % 2 ^ (U - q).toNat != 0

def topExp (m : ℕ) (q : ℤ) : ℤ := q + ((Nat.log2 m + 1 : ℕ) : ℤ) - 1

def tinyFlag (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (sign : Bool)
    (m : ℕ) (q : ℤ) : Bool :=
  let Uu : ℤ := topExp m q - fmt.fracBits
  match sp.tininess with
  | .beforeRounding => decide (Uu < fmt.minQ)
  | .afterRounding =>
    if fmt.minQ ≤ Uu then false
    else if Uu ≤ q then true
    else
      let d := 2 ^ (Uu - q).toNat
      let quot := m / d
      let mu := if roundIncr rm sign quot (m % d) d then quot + 1 else quot
      if mu = 2 ^ fmt.sigBits then Uu + 1 < fmt.minQ else true

def packBody (fmt : Format) (rm : RoundingDirection) (sign : Bool) (m'' : ℕ) (U' : ℤ)
    (inexact tiny : Bool) : ℕ × StatusFlags :=
  if m'' = 0 then
    (fmt.pack sign 0 0, { underflow := true, inexact := true })
  else if m'' < 2 ^ fmt.fracBits then
    (fmt.pack sign 0 m'', { underflow := inexact, inexact })
  else
    let be : ℤ := U' + fmt.fracBits + fmt.bias
    if fmt.expMax ≤ be then
      fmt.overflowResult rm sign
    else
      (fmt.pack sign be.toNat (m'' - 2 ^ fmt.fracBits), { underflow := inexact && tiny, inexact })

def packRounded (fmt : Format) (rm : RoundingDirection) (sign : Bool) (m' : ℕ) (U : ℤ)
    (inexact tiny : Bool) : ℕ × StatusFlags :=
  packBody fmt rm sign (if m' = 2 ^ fmt.sigBits then 2 ^ fmt.fracBits else m')
    (if m' = 2 ^ fmt.sigBits then U + 1 else U) inexact tiny

private theorem ite_pair_fst {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).1 = if c then x.1 else y.1 := by split_ifs <;> rfl

private theorem ite_pair_snd {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by split_ifs <;> rfl

theorem roundPack_eq (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (sign : Bool)
    (m : ℕ) (q : ℤ) :
    fmt.roundPack sp rm sign m q =
      packRounded fmt rm sign (roundAt rm sign m q (max (topExp m q - fmt.fracBits) fmt.minQ))
        (max (topExp m q - fmt.fracBits) fmt.minQ)
        (inexactAt m q (max (topExp m q - fmt.fracBits) fmt.minQ)) (tinyFlag sp fmt rm sign m q) := by
  simp only [Format.roundPack, ite_pair_fst, ite_pair_snd]
  rfl

private theorem two_zpow_div (q U : ℤ) : (2 : ℝ) ^ q / 2 ^ U = 2 ^ (q - U) := by
  rw [zpow_sub₀ two_ne_zero]

theorem roundAt_eq_roundAbs (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) :
    ((roundAt rm sign m q U : ℕ) : ℤ) = roundAbs rm sign ((m : ℝ) * 2 ^ q / 2 ^ U) := by
  unfold roundAt
  split_ifs with h
  · have hk : (((q - U).toNat : ℕ) : ℤ) = q - U := Int.toNat_of_nonneg (by omega)
    have : (m : ℝ) * 2 ^ q / 2 ^ U = ((m * 2 ^ (q - U).toNat : ℕ) : ℝ) := by
      rw [mul_div_assoc, two_zpow_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        ← zpow_natCast, hk]
    rw [this, roundAbs_natCast, Nat.shiftLeft_eq]
  · have hk : (((U - q).toNat : ℕ) : ℤ) = U - q := Int.toNat_of_nonneg (by omega)
    have : (m : ℝ) * 2 ^ q / 2 ^ U = (m : ℝ) / ((2 ^ (U - q).toNat : ℕ) : ℝ) := by
      rw [mul_div_assoc, two_zpow_div, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hk,
        div_eq_mul_inv, ← zpow_neg, neg_sub]
    rw [this]
    exact roundIncr_eq_roundAbs rm sign m _ (by positivity)

private theorem roundIncr_rem_zero (rm : RoundingDirection) (sign : Bool) (quot d : ℕ)
    (hd : 0 < d) : roundIncr rm sign quot 0 d = false := by
  cases rm <;> cases sign <;> simp [roundIncr] <;> omega

theorem roundAt_mul_eq_iff (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) :
    (roundAt rm sign m q U : ℝ) * 2 ^ U = m * 2 ^ q ↔ inexactAt m q U = false := by
  unfold roundAt inexactAt
  split_ifs with h
  · have hk : (((q - U).toNat : ℕ) : ℤ) = q - U := Int.toNat_of_nonneg (by omega)
    simp only [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, iff_true]
    rw [← zpow_natCast, hk, mul_assoc, ← zpow_add₀ two_ne_zero, sub_add_cancel]
  · have hk : (((U - q).toNat : ℕ) : ℤ) = U - q := Int.toNat_of_nonneg (by omega)
    set d := 2 ^ (U - q).toNat with hd_def
    have hd : 0 < d := by positivity
    have h2U : (2 : ℝ) ^ U = (d : ℝ) * 2 ^ q := by
      rw [hd_def, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hk, ← zpow_add₀ two_ne_zero,
        sub_add_cancel]
    have key : ∀ n : ℕ, (n : ℝ) * 2 ^ U = m * 2 ^ q ↔ n * d = m := by
      intro n
      rw [h2U, ← mul_assoc, mul_left_inj' (by positivity : (2 : ℝ) ^ q ≠ 0)]
      exact_mod_cast Iff.rfl
    dsimp only
    rw [key]
    have hdm := Nat.div_add_mod m d
    have hlt := Nat.mod_lt m hd
    by_cases hr : m % d = 0
    · rw [hr, roundIncr_rem_zero rm sign _ d hd]
      simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, iff_true]
      rw [hr] at hdm; rw [mul_comm]; omega
    · have hb : (m % d != 0) = true := by simpa using hr
      rw [hb]
      simp only [Bool.true_eq_false, iff_false]
      split_ifs
      · rw [add_mul, one_mul, mul_comm]; omega
      · rw [mul_comm]; omega

theorem le_roundAt (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) (k : ℕ)
    (h : (2 : ℝ) ^ k * 2 ^ U ≤ m * 2 ^ q) : 2 ^ k ≤ roundAt rm sign m q U := by
  have h1 := roundAt_eq_roundAbs rm sign m q U
  have h2 := floor_le_roundAbs rm sign ((m : ℝ) * 2 ^ q / 2 ^ U)
  have h3 : ((2 ^ k : ℕ) : ℤ) ≤ ⌊(m : ℝ) * 2 ^ q / 2 ^ U⌋ := by
    rw [Int.le_floor, le_div_iff₀ (by positivity)]; push_cast; exact h
  have : ((2 ^ k : ℕ) : ℤ) ≤ (roundAt rm sign m q U : ℤ) := by omega
  exact_mod_cast this

theorem roundAt_le (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) (k : ℕ)
    (h : (m : ℝ) * 2 ^ q ≤ 2 ^ k * 2 ^ U) : roundAt rm sign m q U ≤ 2 ^ k := by
  have h1 := roundAt_eq_roundAbs rm sign m q U
  have h2 := roundAbs_le_ceil rm sign ((m : ℝ) * 2 ^ q / 2 ^ U)
  have h3 : ⌈(m : ℝ) * 2 ^ q / 2 ^ U⌉ ≤ ((2 ^ k : ℕ) : ℤ) := by
    rw [Int.ceil_le, div_le_iff₀ (by positivity)]; push_cast; exact h
  have : (roundAt rm sign m q U : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by omega
  exact_mod_cast this

theorem le_roundAt_succ (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q U : ℤ) (k : ℕ)
    (hlt : (m : ℝ) * 2 ^ q < 2 ^ (k + 1) * 2 ^ U) (h : roundAt rm sign m q U = 2 ^ (k + 1)) :
    2 ^ k ≤ roundAt rm sign m q (U + 1) := by
  have h1 := roundAt_eq_roundAbs rm sign m q U
  have h1' := roundAt_eq_roundAbs rm sign m q (U + 1)
  have hy : (m : ℝ) * 2 ^ q / 2 ^ U < 2 * ((2 ^ k : ℕ) : ℤ) := by
    rw [div_lt_iff₀ (by positivity)]; push_cast
    rw [pow_succ] at hlt; linarith
  have hr : roundAbs rm sign ((m : ℝ) * 2 ^ q / 2 ^ U) = 2 * ((2 ^ k : ℕ) : ℤ) := by
    rw [← h1, h]; push_cast; ring
  have h2 := le_roundAbs_half rm sign _ _ hy hr
  have h3 : (m : ℝ) * 2 ^ q / 2 ^ U / 2 = (m : ℝ) * 2 ^ q / 2 ^ (U + 1) := by
    rw [zpow_add_one₀ two_ne_zero]; ring
  rw [h3, ← h1'] at h2
  exact_mod_cast h2

end SoftFloat.Proof
