/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.RoundPack

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem packRounded_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (sign : Bool) (x : ℝ) (zn : Bool) (m' : ℕ) (U : ℤ) (inexact tiny : Bool)
    (hx0 : x ≠ 0) (hsign : x < 0 ↔ sign = true)
    (hround : roundR fmt rm x = (if sign then -1 else 1) * (m' : ℝ) * 2 ^ U)
    (hinexact : inexact = true ↔ roundR fmt rm x ≠ x)
    (hU : fmt.minQ ≤ U) (hle : m' ≤ 2 ^ fmt.sigBits)
    (hsub : m' < 2 ^ fmt.fracBits → U = fmt.minQ ∧ Tiny sp fmt rm x)
    (htiny : 2 ^ fmt.fracBits ≤ m' → (tiny = true ↔ Tiny sp fmt rm x)) :
    RoundedResultOf sp fmt rm x zn (packRounded fmt rm sign m' U inexact tiny) := by
  have hs := sigBits_eq_fracBits_add_one fmt
  have hN := Nat.two_pow_pos fmt.fracBits
  have h2N : 2 ^ fmt.sigBits = 2 * 2 ^ fmt.fracBits := by rw [hs, pow_succ]; ring
  unfold packRounded
  split_ifs with hc
  · refine packBody_spec sp fmt rm sign x zn _ _ inexact tiny hx0 hsign ?_ hinexact (by omega)
      (by omega) (fun h => absurd h (lt_irrefl _)) (fun _ => htiny (by omega))
    rw [hround, hc, h2N, zpow_add_one₀ two_ne_zero]; push_cast; ring
  · exact packBody_spec sp fmt rm sign x zn _ _ inexact tiny hx0 hsign hround hinexact hU
      (by omega) hsub htiny

theorem two_pow_mul_two_zpow (k : ℕ) (U : ℤ) : (2 : ℝ) ^ k * 2 ^ U = 2 ^ ((k : ℤ) + U) := by
  rw [zpow_add₀ two_ne_zero, zpow_natCast]

theorem topExp_bounds (m : ℕ) (q : ℤ) (hm : 0 < m) :
    (2 : ℝ) ^ topExp m q ≤ m * 2 ^ q ∧ (m : ℝ) * 2 ^ q < 2 ^ (topExp m q + 1) := by
  have hT : topExp m q = (Nat.log2 m : ℤ) + q := by unfold topExp; push_cast; ring
  have h1 : 2 ^ Nat.log2 m ≤ m := Nat.log2_self_le (by omega)
  have h2 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  rw [hT, add_assoc, add_comm q 1, ← add_assoc]
  rw [← two_pow_mul_two_zpow, show ((Nat.log2 m : ℤ) + 1) = ((Nat.log2 m + 1 : ℕ) : ℤ) by push_cast; ring,
    ← two_pow_mul_two_zpow]
  constructor
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by positivity)
  · exact mul_lt_mul_of_pos_right (by exact_mod_cast h2) (by positivity)

theorem abs_signed (sign : Bool) (m : ℕ) (q : ℤ) :
    |(if sign then -1 else 1) * (m : ℝ) * 2 ^ q| = m * 2 ^ q := by
  rw [mul_assoc]; exact abs_sign_mul sign _ (by positivity)

theorem signed_neg_iff (sign : Bool) (m : ℕ) (q : ℤ) (hm : 0 < m) :
    (if sign then -1 else 1) * (m : ℝ) * 2 ^ q < 0 ↔ sign = true := by
  have : (0 : ℝ) < m * 2 ^ q := by have : (0 : ℝ) < m := by exact_mod_cast hm
                                   positivity
  cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, iff_false, not_lt,
    neg_mul, neg_lt_zero, iff_true] <;> linarith

theorem signed_ne_zero (sign : Bool) (m : ℕ) (q : ℤ) (hm : 0 < m) :
    (if sign then -1 else 1) * (m : ℝ) * 2 ^ q ≠ 0 := by
  rw [← abs_ne_zero, abs_signed]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem magR_signed (sign : Bool) (m : ℕ) (q : ℤ) (hm : 0 < m) :
    magR ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q) = topExp m q + 1 := by
  obtain ⟨h1, h2⟩ := topExp_bounds m q hm
  have hpos : (0 : ℝ) < m * 2 ^ q := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hle := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hpos).mp (by exact_mod_cast h1)
  have hlt := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by exact_mod_cast h2)
  unfold magR; rw [abs_signed]; omega

theorem signed_round_eq (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q c : ℤ) (hm : 0 < m) :
    (if (if sign then -1 else 1) * (m : ℝ) * 2 ^ q < 0 then -1 else 1)
      * ((roundAbs rm (decide ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q < 0))
          (|(if sign then -1 else 1) * (m : ℝ) * 2 ^ q| / 2 ^ c) : ℤ) : ℝ) * 2 ^ c
      = (if sign then -1 else 1) * (roundAt rm sign m q c : ℝ) * 2 ^ c := by
  have hn := signed_neg_iff sign m q hm
  have hd : decide ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q < 0) = sign := by
    simp only [hn, Bool.decide_eq_true]
  have hn' : (if (if sign then -1 else 1) * (m : ℝ) * 2 ^ q < 0 then (-1 : ℝ) else 1)
      = if sign then -1 else 1 := by
    simp only [hn]
  rw [abs_signed, hd, hn', ← roundAt_eq_roundAbs, Int.cast_natCast]

theorem roundR_signed (fmt : Format) (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q : ℤ)
    (hm : 0 < m) :
    roundR fmt rm ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q)
      = (if sign then -1 else 1)
        * (roundAt rm sign m q (max (topExp m q - fmt.fracBits) fmt.minQ) : ℝ)
        * 2 ^ (max (topExp m q - fmt.fracBits) fmt.minQ) := by
  have hc : cexpR fmt ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q)
      = max (topExp m q - fmt.fracBits) fmt.minQ := by
    unfold cexpR; rw [magR_signed sign m q hm, fracBits_cast]; congr 1; ring
  unfold roundR; rw [hc]; exact signed_round_eq rm sign m q _ hm

theorem roundRInf_signed (fmt : Format) (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q : ℤ)
    (hm : 0 < m) :
    roundRInf fmt rm ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q)
      = (if sign then -1 else 1) * (roundAt rm sign m q (topExp m q - fmt.fracBits) : ℝ)
        * 2 ^ (topExp m q - fmt.fracBits) := by
  have hc : cexpRInf fmt ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q)
      = topExp m q - fmt.fracBits := by
    unfold cexpRInf; rw [magR_signed sign m q hm, fracBits_cast]; ring
  unfold roundRInf; rw [hc]; exact signed_round_eq rm sign m q _ hm

theorem tiny_after_iff (fmt : Format) (rm : RoundingDirection) (sign : Bool) (m : ℕ) (q : ℤ)
    (hm : 0 < m) :
    |roundRInf fmt rm ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q)| < 2 ^ emin fmt ↔
      (roundAt rm sign m q (topExp m q - fmt.fracBits) : ℝ) * 2 ^ (topExp m q - fmt.fracBits)
        < 2 ^ emin fmt := by
  rw [roundRInf_signed fmt rm sign m q hm, mul_assoc, abs_sign_mul sign _ (by positivity)]

theorem tinyFlag_iff (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (sign : Bool)
    (m : ℕ) (q : ℤ) (hm : 0 < m) :
    tinyFlag sp fmt rm sign m q = true ↔
      Tiny sp fmt rm ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q) := by
  have h12 : (1 : ℝ) < 2 := one_lt_two
  have hs := sigBits_eq_fracBits_add_one fmt
  have hmin := minQ_add_fracBits fmt
  obtain ⟨hlo, hhi⟩ := topExp_bounds m q hm
  have hx0 := signed_ne_zero sign m q hm
  unfold tinyFlag Tiny
  simp only [hx0, ne_eq, not_false_eq_true, true_and]
  cases ht : sp.tininess
  · -- 丸めの前
    simp only [decide_eq_true_eq]
    rw [abs_signed]
    constructor
    · intro h
      calc (m : ℝ) * 2 ^ q < 2 ^ (topExp m q + 1) := hhi
        _ ≤ 2 ^ emin fmt := (zpow_le_zpow_iff_right₀ h12).mpr (by omega)
    · intro h
      have := (zpow_lt_zpow_iff_right₀ h12).mp (lt_of_le_of_lt hlo h)
      omega
  · -- 丸めの後
    rw [tiny_after_iff fmt rm sign m q hm]
    set Uu := topExp m q - fmt.fracBits with hUu
    have hT : topExp m q = (fmt.fracBits : ℤ) + Uu := by omega
    have hup : (m : ℝ) * 2 ^ q ≤ 2 ^ fmt.sigBits * 2 ^ Uu := by
      rw [two_pow_mul_two_zpow, hs]; push_cast
      rw [show (fmt.fracBits : ℤ) + 1 + Uu = topExp m q + 1 by omega]; exact hhi.le
    have hle := roundAt_le rm sign m q Uu fmt.sigBits hup
    by_cases h1 : fmt.minQ ≤ Uu
    · simp only [h1, ↓reduceIte, Bool.false_eq_true, false_iff, not_lt]
      have hlo' : (2 : ℝ) ^ fmt.fracBits * 2 ^ Uu ≤ m * 2 ^ q := by
        rw [two_pow_mul_two_zpow, ← hT]; exact hlo
      have hge := le_roundAt rm sign m q Uu fmt.fracBits hlo'
      calc (2 : ℝ) ^ emin fmt ≤ 2 ^ ((fmt.fracBits : ℤ) + Uu) :=
            (zpow_le_zpow_iff_right₀ h12).mpr (by omega)
        _ = 2 ^ fmt.fracBits * 2 ^ Uu := (two_pow_mul_two_zpow _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hge) (by positivity)
    · simp only [h1, ↓reduceIte]
      have hlt_emin : (2 : ℝ) ^ fmt.sigBits * 2 ^ Uu ≤ 2 ^ emin fmt := by
        rw [two_pow_mul_two_zpow]; exact (zpow_le_zpow_iff_right₀ h12).mpr (by omega)
      by_cases h2 : Uu ≤ q
      · simp only [h2, ↓reduceIte, true_iff]
        have hex := (roundAt_mul_eq_iff rm sign m q Uu).mpr (by simp [inexactAt, h2])
        rw [hex]
        calc (m : ℝ) * 2 ^ q < 2 ^ (topExp m q + 1) := hhi
          _ ≤ 2 ^ emin fmt := (zpow_le_zpow_iff_right₀ h12).mpr (by omega)
      · have hmu : (let d := 2 ^ (Uu - q).toNat
            let quot := m / d
            if roundIncr rm sign quot (m % d) d then quot + 1 else quot)
            = roundAt rm sign m q Uu := by simp [roundAt, h2]
        simp only [h2, ↓reduceIte]
        simp only at hmu
        rw [hmu]
        by_cases h3 : roundAt rm sign m q Uu = 2 ^ fmt.sigBits
        · simp only [h3, ↓reduceIte, decide_eq_true_eq]
          rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_mul_two_zpow,
            zpow_lt_zpow_iff_right₀ h12]
          omega
        · simp only [h3, ↓reduceIte, true_iff]
          have h4 : roundAt rm sign m q Uu < 2 ^ fmt.sigBits := by omega
          have h4' : (roundAt rm sign m q Uu : ℝ) < 2 ^ fmt.sigBits := by exact_mod_cast h4
          exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h4' (by positivity)) hlt_emin

theorem tiny_of_roundAt_lt (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (sign : Bool) (m : ℕ) (q : ℤ) (hm : 0 < m)
    (h : roundAt rm sign m q (max (topExp m q - fmt.fracBits) fmt.minQ) < 2 ^ fmt.fracBits) :
    max (topExp m q - fmt.fracBits) fmt.minQ = fmt.minQ ∧
      Tiny sp fmt rm ((if sign then -1 else 1) * (m : ℝ) * 2 ^ q) := by
  have h12 : (1 : ℝ) < 2 := one_lt_two
  have hs := sigBits_eq_fracBits_add_one fmt
  have hmin := minQ_add_fracBits fmt
  obtain ⟨hlo, hhi⟩ := topExp_bounds m q hm
  have hsmall : topExp m q - fmt.fracBits < fmt.minQ := by
    by_contra hc
    have hU : max (topExp m q - fmt.fracBits) fmt.minQ = topExp m q - fmt.fracBits :=
      max_eq_left (by omega)
    rw [hU] at h
    have hlo' : (2 : ℝ) ^ fmt.fracBits * 2 ^ (topExp m q - fmt.fracBits) ≤ m * 2 ^ q := by
      rw [two_pow_mul_two_zpow]; ring_nf; exact hlo
    have := le_roundAt rm sign m q _ fmt.fracBits hlo'
    omega
  have hU : max (topExp m q - fmt.fracBits) fmt.minQ = fmt.minQ := max_eq_right (by omega)
  refine ⟨hU, ?_⟩
  rw [← tinyFlag_iff sp fmt rm sign m q hm]
  unfold tinyFlag
  rw [hU] at h
  cases ht : sp.tininess
  · simp only [decide_eq_true_eq]; exact hsmall
  · simp only [show ¬ fmt.minQ ≤ topExp m q - fmt.fracBits by omega, ↓reduceIte]
    by_cases h2 : topExp m q - fmt.fracBits ≤ q
    · simp only [h2, ↓reduceIte]
    · have hmu : (let d := 2 ^ (topExp m q - fmt.fracBits - q).toNat
          let quot := m / d
          if roundIncr rm sign quot (m % d) d then quot + 1 else quot)
          = roundAt rm sign m q (topExp m q - fmt.fracBits) := by simp [roundAt, h2]
      simp only [h2, ↓reduceIte]
      simp only at hmu
      rw [hmu]
      by_cases h3 : roundAt rm sign m q (topExp m q - fmt.fracBits) = 2 ^ fmt.sigBits
      · simp only [h3, ↓reduceIte, decide_eq_true_eq]
        by_contra h4
        have hUu : topExp m q - fmt.fracBits + 1 = fmt.minQ := by omega
        rw [hs] at h3
        have hlt : (m : ℝ) * 2 ^ q < 2 ^ (fmt.fracBits + 1) * 2 ^ (topExp m q - fmt.fracBits) := by
          rw [two_pow_mul_two_zpow]; push_cast; ring_nf; ring_nf at hhi; exact hhi
        have := le_roundAt_succ rm sign m q _ fmt.fracBits hlt h3
        rw [hUu] at this
        omega
      · simp only [h3, ↓reduceIte]

theorem roundPack_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (sign : Bool)
    (m : ℕ) (q : ℤ) (hm : 0 < m) (zn : Bool) :
    RoundedResultOf sp fmt rm ((if sign then -1 else 1) * (m : ℝ) * (2 : ℝ) ^ q) zn
      (fmt.roundPack sp rm sign m q) := by
  have hs := sigBits_eq_fracBits_add_one fmt
  obtain ⟨hlo, hhi⟩ := topExp_bounds m q hm
  rw [roundPack_eq]
  have hround := roundR_signed fmt rm sign m q hm
  refine packRounded_spec sp fmt rm sign _ zn _ _ _ _ (signed_ne_zero sign m q hm)
    (signed_neg_iff sign m q hm) hround ?_ (le_max_right _ _) ?_
    (tiny_of_roundAt_lt sp fmt rm sign m q hm)
    (fun _ => tinyFlag_iff sp fmt rm sign m q hm)
  · rw [hround, ne_eq, ← Bool.not_eq_false, ← roundAt_mul_eq_iff rm sign m q]
    have : (if sign then -1 else 1 : ℝ) ≠ 0 := by split_ifs <;> norm_num
    rw [mul_assoc, mul_assoc, mul_right_inj' this]
  · apply roundAt_le
    rw [two_pow_mul_two_zpow, hs]
    calc (m : ℝ) * 2 ^ q ≤ 2 ^ (topExp m q + 1) := hhi.le
      _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)

end SoftFloat.Proof
