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

def SameAtScale (e : ℤ) (x y : ℝ) : Prop :=
  ∀ n : ℤ, ((n : ℝ) * 2 ^ e ≤ x ↔ (n : ℝ) * 2 ^ e ≤ y) ∧ (x ≤ n * 2 ^ e ↔ y ≤ n * 2 ^ e)

namespace SameAtScale

variable {e c : ℤ} {x y : ℝ}

theorem symm (h : SameAtScale e x y) : SameAtScale e y x :=
  fun n => ⟨(h n).1.symm, (h n).2.symm⟩

theorem lt_iff (h : SameAtScale e x y) (n : ℤ) : x < n * 2 ^ e ↔ y < n * 2 ^ e := by
  rw [← not_le, ← not_le, (h n).1]

theorem gt_iff (h : SameAtScale e x y) (n : ℤ) : (n : ℝ) * 2 ^ e < x ↔ (n : ℝ) * 2 ^ e < y := by
  rw [← not_le, ← not_le, (h n).2]

theorem eq_iff (h : SameAtScale e x y) (n : ℤ) : x = n * 2 ^ e ↔ y = n * 2 ^ e := by
  rw [le_antisymm_iff, le_antisymm_iff, (h n).1, (h n).2]

theorem neg (h : SameAtScale e x y) : SameAtScale e (-x) (-y) := by
  intro n
  have h' := h (-n)
  push_cast at h'
  constructor
  · exact ⟨fun hh => by have := h'.2.1 (by linarith); linarith,
      fun hh => by have := h'.2.2 (by linarith); linarith⟩
  · exact ⟨fun hh => by have := h'.1.1 (by linarith); linarith,
      fun hh => by have := h'.1.2 (by linarith); linarith⟩

theorem nonneg_iff (h : SameAtScale e x y) : 0 ≤ x ↔ 0 ≤ y := by
  simpa using (h 0).1

theorem neg_iff (h : SameAtScale e x y) : x < 0 ↔ y < 0 := by
  simpa using h.lt_iff 0

theorem zero_iff (h : SameAtScale e x y) : x = 0 ↔ y = 0 := by
  simpa using h.eq_iff 0

theorem abs (h : SameAtScale e x y) : SameAtScale e |x| |y| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (h.nonneg_iff.1 hx)]; exact h
  · have hy : ¬ 0 ≤ y := fun hy => hx (h.nonneg_iff.2 hy)
    rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]; exact h.neg

theorem zpow_eq_mul (hec : e ≤ c) (n : ℤ) :
    (n : ℝ) * 2 ^ c = ((n * 2 ^ (c - e).toNat : ℤ) : ℝ) * 2 ^ e := by
  push_cast
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
  congr 2; omega

theorem eq_iff' (h : SameAtScale e x y) (hec : e ≤ c) (n : ℤ) :
    x = n * 2 ^ c ↔ y = n * 2 ^ c := by
  rw [zpow_eq_mul hec n]; exact h.eq_iff _

theorem lt_iff' (h : SameAtScale e x y) (hec : e ≤ c) (n : ℤ) :
    x < n * 2 ^ c ↔ y < n * 2 ^ c := by
  rw [zpow_eq_mul hec n]; exact h.lt_iff _

theorem mono (h : SameAtScale e x y) (hec : e ≤ c) : SameAtScale c x y := by
  intro n
  rw [zpow_eq_mul hec n]
  exact h _

theorem floor_div_eq (h : SameAtScale c x y) : ⌊x / 2 ^ c⌋ = ⌊y / 2 ^ c⌋ := by
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have key : ∀ n : ℤ, n ≤ ⌊x / 2 ^ c⌋ ↔ n ≤ ⌊y / 2 ^ c⌋ := by
    intro n
    rw [Int.le_floor, Int.le_floor, le_div_iff₀ hp, le_div_iff₀ hp]
    exact (h n).1
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem ceil_div_eq (h : SameAtScale c x y) : ⌈x / 2 ^ c⌉ = ⌈y / 2 ^ c⌉ := by
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have key : ∀ n : ℤ, ⌈x / 2 ^ c⌉ ≤ n ↔ ⌈y / 2 ^ c⌉ ≤ n := by
    intro n
    rw [Int.ceil_le, Int.ceil_le, div_le_iff₀ hp, div_le_iff₀ hp]
    exact (h n).2
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem half_sub_lt_iff (x : ℝ) (c fl : ℤ) :
    x / 2 ^ c - fl < 1 / 2 ↔ x < ((2 * fl + 1 : ℤ) : ℝ) * 2 ^ (c - 1) := by
  have hp : (0 : ℝ) < 2 ^ (c - 1) := by positivity
  have hc : (2 : ℝ) ^ c = 2 * 2 ^ (c - 1) := by
    rw [← zpow_one_add₀ two_ne_zero]; congr 1; ring
  rw [hc, sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
  push_cast
  constructor <;> intro h <;> nlinarith

theorem half_lt_sub_iff (x : ℝ) (c fl : ℤ) :
    1 / 2 < x / 2 ^ c - fl ↔ ((2 * fl + 1 : ℤ) : ℝ) * 2 ^ (c - 1) < x := by
  have hp : (0 : ℝ) < 2 ^ (c - 1) := by positivity
  have hc : (2 : ℝ) ^ c = 2 * 2 ^ (c - 1) := by
    rw [← zpow_one_add₀ two_ne_zero]; congr 1; ring
  rw [hc, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  push_cast
  constructor <;> intro h <;> nlinarith

theorem half_le_sub_iff (x : ℝ) (c fl : ℤ) :
    1 / 2 ≤ x / 2 ^ c - fl ↔ ((2 * fl + 1 : ℤ) : ℝ) * 2 ^ (c - 1) ≤ x := by
  rw [← not_lt, ← not_lt, half_sub_lt_iff]

theorem roundAbs_div_eq (h : SameAtScale (c - 1) x y) (rm : RoundingDirection) (neg : Bool) :
    roundAbs rm neg (x / 2 ^ c) = roundAbs rm neg (y / 2 ^ c) := by
  have hc : SameAtScale c x y := h.mono (by omega)
  have hfl := hc.floor_div_eq
  have hcl := hc.ceil_div_eq
  cases rm with
  | roundTiesToEven =>
    simp only [roundAbs, roundMagTiesToEven, hfl, half_sub_lt_iff, half_lt_sub_iff, h.lt_iff, h.gt_iff]
  | roundTiesToAway =>
    simp only [roundAbs, roundMagTiesToAway]
    rw [hfl]
    exact if_congr ((half_le_sub_iff _ _ _).trans ((h _).1.trans (half_le_sub_iff _ _ _).symm))
      rfl rfl
  | roundTowardZero => simp only [roundAbs, roundMagDown, hfl]
  | roundTowardNegative => simp only [roundAbs, roundMagDown, roundMagUp, hfl, hcl]
  | roundTowardPositive => simp only [roundAbs, roundMagDown, roundMagUp, hfl, hcl]
  | roundToOdd => simp only [roundAbs, roundMagToOdd_eq, hfl, hcl]

theorem log_abs_eq (h : SameAtScale e x y) {K : ℕ} (hx : (2 : ℝ) ^ (e + K) ≤ |x|) :
    Int.log 2 |x| = Int.log 2 |y| := by
  have ha := h.abs
  have hK : (2 : ℝ) ^ (e + K) = ((2 ^ K : ℕ) : ℤ) * 2 ^ e := by
    push_cast; rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm]
  have hy : (2 : ℝ) ^ (e + K) ≤ |y| := by rw [hK] at hx ⊢; exact (ha _).1.1 hx
  have hxp : 0 < |x| := lt_of_lt_of_le (by positivity) hx
  have hyp : 0 < |y| := lt_of_lt_of_le (by positivity) hy
  have hlx := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxp).mp (by exact_mod_cast hx)
  have hly := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hyp).mp (by exact_mod_cast hy)
  have key : ∀ j : ℤ, j ≤ Int.log 2 |x| ↔ j ≤ Int.log 2 |y| := by
    intro j
    by_cases hj : j ≤ e
    · exact ⟨fun _ => by omega, fun _ => by omega⟩
    · rw [← Int.zpow_le_iff_le_log (by norm_num) hxp, ← Int.zpow_le_iff_le_log (by norm_num) hyp]
      have hj' : ((2 : ℕ) : ℝ) ^ j = ((1 : ℤ) : ℝ) * 2 ^ j := by push_cast; ring
      rw [hj', zpow_eq_mul (show e ≤ j by omega)]
      exact (ha _).1
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem magR_eq (h : SameAtScale e x y) {K : ℕ} (hx : (2 : ℝ) ^ (e + K) ≤ |x|) :
    magR x = magR y := by
  unfold magR; rw [h.log_abs_eq hx]

theorem le_log_abs {K : ℕ} (hx : (2 : ℝ) ^ (e + K) ≤ |x|) : e + K ≤ Int.log 2 |x| := by
  have hxp : 0 < |x| := lt_of_lt_of_le (by positivity) hx
  exact (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hxp).mp (by exact_mod_cast hx)

theorem roundR_eq (h : SameAtScale e x y) (fmt : Format) (rm : RoundingDirection)
    (hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |x|) : roundR fmt rm x = roundR fmt rm y := by
  have hc : cexpR fmt x = cexpR fmt y := by unfold cexpR; rw [h.magR_eq hx]
  have hle : e ≤ cexpR fmt x - 1 := by
    have := le_log_abs hx
    unfold cexpR magR; omega
  unfold roundR
  rw [← hc, (h.abs.mono hle).roundAbs_div_eq]; simp only [h.neg_iff]

theorem roundRInf_eq (h : SameAtScale e x y) (fmt : Format) (rm : RoundingDirection)
    (hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |x|) : roundRInf fmt rm x = roundRInf fmt rm y := by
  have hc : cexpRInf fmt x = cexpRInf fmt y := by unfold cexpRInf; rw [h.magR_eq hx]
  have hle : e ≤ cexpRInf fmt x - 1 := by
    have := le_log_abs hx
    unfold cexpRInf magR; omega
  unfold roundRInf
  rw [← hc, (h.abs.mono hle).roundAbs_div_eq]; simp only [h.neg_iff]

theorem roundR_eq_intCast_mul (fmt : Format) (rm : RoundingDirection) (x : ℝ) :
    ∃ n : ℤ, roundR fmt rm x = n * 2 ^ cexpR fmt x := by
  refine ⟨(if x < 0 then -1 else 1) * roundAbs rm (decide (x < 0)) (|x| / 2 ^ cexpR fmt x), ?_⟩
  unfold roundR; split_ifs <;> push_cast <;> ring

theorem roundR_eq_self_iff (h : SameAtScale e x y) (fmt : Format) (rm : RoundingDirection)
    (hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |x|) : roundR fmt rm x = x ↔ roundR fmt rm y = y := by
  have hle : e ≤ cexpR fmt x := by
    have := le_log_abs hx
    unfold cexpR magR; omega
  rw [← h.roundR_eq fmt rm hx]
  obtain ⟨n, hn⟩ := roundR_eq_intCast_mul fmt rm x
  rw [hn, eq_comm, h.eq_iff' hle, eq_comm]

theorem tiny_iff (h : SameAtScale e x y) (sp : Specialization) (fmt : Format)
    (rm : RoundingDirection) (hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |x|) :
    Tiny sp fmt rm x ↔ Tiny sp fmt rm y := by
  unfold Tiny
  rw [h.roundRInf_eq fmt rm hx, ne_eq, ne_eq, h.zero_iff]
  cases sp.tininess
  · simp only
    by_cases he : e ≤ emin fmt
    · have := h.abs.lt_iff' he (1 : ℤ)
      simp only [Int.cast_one, one_mul] at this
      rw [this]
    · have hy : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |y| := by
        have hK : (2 : ℝ) ^ (e + fmt.sigBits) = ((2 ^ fmt.sigBits : ℕ) : ℤ) * 2 ^ e := by
          push_cast; rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm]
        rw [hK] at hx ⊢; exact (h.abs _).1.1 hx
      have hlt : (2 : ℝ) ^ emin fmt ≤ 2 ^ (e + fmt.sigBits) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      constructor <;> intro hh <;> refine ⟨hh.1, ?_⟩ <;> linarith [hh.2]
  · rfl

theorem roundedResultOf_iff (h : SameAtScale e x y) (sp : Specialization) (fmt : Format)
    (rm : RoundingDirection) (zn : Bool) (r : ℕ × StatusFlags)
    (hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |x|) :
    RoundedResultOf sp fmt rm x zn r ↔ RoundedResultOf sp fmt rm y zn r := by
  have hR := h.roundR_eq fmt rm hx
  have hE := h.roundR_eq_self_iff fmt rm hx
  have hT := h.tiny_iff sp fmt rm hx
  have hn := h.neg_iff
  have hz := h.zero_iff
  unfold RoundedResultOf
  rw [hR]
  rw [hR] at hE
  have hE' : roundR fmt rm y ≠ x ↔ roundR fmt rm y ≠ y := not_congr hE
  simp only [hn, hz, hE', hT]

end SameAtScale

theorem natCast_mul_zpow_le_iff (n : ℤ) (Q : ℕ) (e : ℤ) :
    (n : ℝ) * 2 ^ e ≤ (Q : ℝ) * 2 ^ e ↔ n ≤ Q := by
  rw [mul_le_mul_iff_left₀ (by positivity)]; exact_mod_cast Iff.rfl

theorem bracket_ge_iff {Q : ℕ} {e : ℤ} {v : ℝ} (hlo : (Q : ℝ) * 2 ^ e ≤ v)
    (hhi : v < ((Q : ℝ) + 1) * 2 ^ e) (n : ℤ) : (n : ℝ) * 2 ^ e ≤ v ↔ n ≤ Q := by
  constructor
  · intro hn
    by_contra hc
    have : ((Q + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast (show (Q : ℤ) + 1 ≤ n by omega)
    push_cast at this
    have : ((Q : ℝ) + 1) * 2 ^ e ≤ n * 2 ^ e := mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  · intro hn
    exact le_trans ((natCast_mul_zpow_le_iff n Q e).2 hn) hlo

theorem intCast_mul_zpow_le_iff (a b : ℤ) (e : ℤ) :
    (a : ℝ) * 2 ^ e ≤ (b : ℝ) * 2 ^ e ↔ a ≤ b := by
  rw [mul_le_mul_iff_left₀ (by positivity)]; exact_mod_cast Iff.rfl

theorem bracket_le_iff {Q : ℕ} {e : ℤ} {v : ℝ} (hlo : (Q : ℝ) * 2 ^ e ≤ v)
    (hhi : v < ((Q : ℝ) + 1) * 2 ^ e) (n : ℤ) :
    v ≤ n * 2 ^ e ↔ (Q : ℤ) < n ∨ (n = Q ∧ v = Q * 2 ^ e) := by
  have hQ : ((Q : ℤ) : ℝ) = Q := Int.cast_natCast Q
  have hQ1 : (((Q : ℤ) + 1 : ℤ) : ℝ) = Q + 1 := by push_cast; ring
  constructor
  · intro hn
    by_cases hc : (Q : ℤ) < n
    · exact Or.inl hc
    · have h2 : (Q : ℤ) ≤ n := by
        rw [← intCast_mul_zpow_le_iff _ _ e, hQ]; exact le_trans hlo hn
      have hnQ : n = Q := by omega
      subst hnQ
      rw [hQ] at hn
      exact Or.inr ⟨rfl, le_antisymm hn hlo⟩
  · rintro (hc | ⟨rfl, hv⟩)
    · have : ((Q : ℤ) + 1 : ℤ) ≤ n := by omega
      rw [← intCast_mul_zpow_le_iff _ _ e, hQ1] at this
      linarith
    · rw [hQ]; exact hv.le

theorem sameAtScale_of_bracket {Q : ℕ} {e : ℤ} {v w : ℝ}
    (hlo : (Q : ℝ) * 2 ^ e ≤ v) (hhi : v < ((Q : ℝ) + 1) * 2 ^ e)
    (hlo' : (Q : ℝ) * 2 ^ e ≤ w) (hhi' : w < ((Q : ℝ) + 1) * 2 ^ e)
    (hex : v = Q * 2 ^ e ↔ w = Q * 2 ^ e) : SameAtScale e v w := by
  intro n
  rw [bracket_ge_iff hlo hhi, bracket_ge_iff hlo' hhi', bracket_le_iff hlo hhi,
    bracket_le_iff hlo' hhi', hex]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem sticky_bracket (Q s : ℕ) (e : ℤ) (hs : s ≤ 1) :
    (Q : ℝ) * 2 ^ e ≤ ((2 * Q + s : ℕ) : ℝ) * 2 ^ (e - 1) ∧
      ((2 * Q + s : ℕ) : ℝ) * 2 ^ (e - 1) < ((Q : ℝ) + 1) * 2 ^ e ∧
      (((2 * Q + s : ℕ) : ℝ) * 2 ^ (e - 1) = Q * 2 ^ e ↔ s = 0) := by
  have he : (2 : ℝ) ^ e = 2 * 2 ^ (e - 1) := by
    rw [← zpow_one_add₀ two_ne_zero]; congr 1; ring
  have hp : (0 : ℝ) < 2 ^ (e - 1) := by positivity
  have hs' : (s : ℝ) ≤ 1 := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := by positivity
  rw [he]
  push_cast
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  constructor
  · intro h
    have : (s : ℝ) * 2 ^ (e - 1) = 0 := by linarith
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hp.ne'
  · intro h; subst h; push_cast; ring

theorem roundedResultOf_roundPack_sticky (sp : Specialization) (fmt : Format)
    (rm : RoundingDirection) (sign : Bool) (v : ℝ) (Q s : ℕ) (e : ℤ) (zn : Bool)
    (hlo : (Q : ℝ) * 2 ^ e ≤ v) (hhi : v < ((Q : ℝ) + 1) * 2 ^ e)
    (hs : s ≤ 1) (hs0 : s = 0 ↔ v = Q * 2 ^ e) (hQ : 2 ^ fmt.sigBits ≤ Q) :
    RoundedResultOf sp fmt rm ((if sign then -1 else 1) * v) zn
      (fmt.roundPack sp rm sign (2 * Q + s) (e - 1)) := by
  obtain ⟨h1, h2, h3⟩ := sticky_bracket Q s e hs
  have hQ0 : 0 < Q := lt_of_lt_of_le (Nat.two_pow_pos _) hQ
  have hsame : SameAtScale e v (((2 * Q + s : ℕ) : ℝ) * 2 ^ (e - 1)) :=
    sameAtScale_of_bracket hlo hhi h1 h2 (by rw [h3, hs0])
  have hsame' : SameAtScale e ((if sign then -1 else 1) * v)
      ((if sign then -1 else 1) * ((2 * Q + s : ℕ) : ℝ) * 2 ^ (e - 1)) := by
    rw [mul_assoc]
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]; exact hsame
    · simp only [↓reduceIte, neg_one_mul]; exact hsame.neg
  have hv0 : 0 ≤ v := le_trans (by positivity) hlo
  have hx : (2 : ℝ) ^ (e + fmt.sigBits) ≤ |(if sign then -1 else 1) * v| := by
    rw [abs_sign_mul sign v hv0]
    refine le_trans ?_ hlo
    rw [add_comm, ← two_pow_mul_two_zpow]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hQ) (by positivity)
  rw [hsame'.roundedResultOf_iff sp fmt rm zn _ hx]
  exact roundPack_spec sp fmt rm sign _ _ (by omega) zn

end SoftFloat.Proof
