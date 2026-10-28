/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Sticky
import SoftFloat.Core.Proof.LogB
import SoftFloat.Core.Proof.ConvertFormat

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem abs_roundR_eq (fmt : Format) (rm : RoundingDirection) (z : ℝ) :
    |roundR fmt rm z| = ((roundAbs rm (decide (z < 0)) (|z| / 2 ^ cexpR fmt z) : ℤ) : ℝ) * 2 ^ cexpR fmt z := by
  have hp : (0 : ℝ) < 2 ^ cexpR fmt z := by positivity
  have hf : 0 ≤ ⌊|z| / 2 ^ cexpR fmt z⌋ := Int.floor_nonneg.2 (div_nonneg (abs_nonneg z) hp.le)
  have hk : (0 : ℝ) ≤ ((roundAbs rm (decide (z < 0)) (|z| / 2 ^ cexpR fmt z) : ℤ) : ℝ) := by
    exact_mod_cast le_trans hf (floor_le_roundAbs _ _ _)
  unfold roundR
  rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hk]
  have : |(if z < 0 then -1 else 1 : ℝ)| = 1 := by split_ifs <;> norm_num
  rw [this, one_mul]

theorem abs_roundRInf_eq (fmt : Format) (rm : RoundingDirection) (z : ℝ) :
    |roundRInf fmt rm z|
      = ((roundAbs rm (decide (z < 0)) (|z| / 2 ^ cexpRInf fmt z) : ℤ) : ℝ) * 2 ^ cexpRInf fmt z := by
  have hp : (0 : ℝ) < 2 ^ cexpRInf fmt z := by positivity
  have hf : 0 ≤ ⌊|z| / 2 ^ cexpRInf fmt z⌋ := Int.floor_nonneg.2 (div_nonneg (abs_nonneg z) hp.le)
  have hk : (0 : ℝ) ≤ ((roundAbs rm (decide (z < 0)) (|z| / 2 ^ cexpRInf fmt z) : ℤ) : ℝ) := by
    exact_mod_cast le_trans hf (floor_le_roundAbs _ _ _)
  unfold roundRInf
  rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hk]
  have : |(if z < 0 then -1 else 1 : ℝ)| = 1 := by split_ifs <;> norm_num
  rw [this, one_mul]

theorem two_pow_le_floor_div {z : ℝ} {c : ℤ} (j : ℕ) (hz : (2 : ℝ) ^ (c + j) ≤ |z|) :
    ((2 ^ j : ℕ) : ℤ) ≤ ⌊|z| / 2 ^ c⌋ := by
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  rw [Int.le_floor, le_div_iff₀ hp]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm]
  exact hz

theorem two_zpow_log_le {z : ℝ} (hz : z ≠ 0) : (2 : ℝ) ^ (magR z - 1) ≤ |z| := by
  have : magR z - 1 = Int.log 2 |z| := by unfold magR; ring
  rw [this]
  exact Int.zpow_log_le_self (b := 2) (by norm_num) (abs_pos.2 hz)

theorem two_zpow_le_abs_roundR (fmt : Format) (rm : RoundingDirection) {k : ℤ} {z : ℝ}
    (hk : fmt.minQ ≤ k) (hz : (2 : ℝ) ^ k ≤ |z|) : (2 : ℝ) ^ k ≤ |roundR fmt rm z| := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, abs_zero] at hz; exact absurd hz (not_le.2 (by positivity))
  have hlog := SameAtScale.le_log_abs (e := k) (K := 0) (by simpa using hz)
  have hm : k ≤ magR z - 1 := by unfold magR; omega
  have hp3 := fmt.sigBits_three_le
  set c := cexpR fmt z with hc
  have hcm : c ≤ magR z - 1 := by
    rw [hc]; unfold cexpR; omega
  set j := (magR z - 1 - c).toNat with hj
  have hj' : c + (j : ℤ) = magR z - 1 := by rw [hj]; omega
  have hfl := two_pow_le_floor_div (c := c) j (by rw [hj']; exact two_zpow_log_le hz0)
  have hge : ((2 ^ j : ℕ) : ℤ) ≤ roundAbs rm (decide (z < 0)) (|z| / 2 ^ c) :=
    le_trans hfl (floor_le_roundAbs _ _ _)
  rw [abs_roundR_eq, ← hc]
  calc (2 : ℝ) ^ k ≤ 2 ^ (magR z - 1) := zpow_le_zpow_right₀ (by norm_num) hm
    _ = ((2 ^ j : ℕ) : ℝ) * 2 ^ c := by
      push_cast; rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm, hj']
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hge

theorem two_zpow_le_abs_roundRInf (fmt : Format) (rm : RoundingDirection) {k : ℤ} {z : ℝ}
    (hz : (2 : ℝ) ^ k ≤ |z|) : (2 : ℝ) ^ k ≤ |roundRInf fmt rm z| := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, abs_zero] at hz; exact absurd hz (not_le.2 (by positivity))
  have hlog := SameAtScale.le_log_abs (e := k) (K := 0) (by simpa using hz)
  have hm : k ≤ magR z - 1 := by unfold magR; omega
  have hp3 := fmt.sigBits_three_le
  set c := cexpRInf fmt z with hc
  have hcm : c ≤ magR z - 1 := by
    rw [hc]; unfold cexpRInf; omega
  set j := (magR z - 1 - c).toNat with hj
  have hj' : c + (j : ℤ) = magR z - 1 := by rw [hj]; omega
  have hfl := two_pow_le_floor_div (c := c) j (by rw [hj']; exact two_zpow_log_le hz0)
  have hge : ((2 ^ j : ℕ) : ℤ) ≤ roundAbs rm (decide (z < 0)) (|z| / 2 ^ c) :=
    le_trans hfl (floor_le_roundAbs _ _ _)
  rw [abs_roundRInf_eq, ← hc]
  calc (2 : ℝ) ^ k ≤ 2 ^ (magR z - 1) := zpow_le_zpow_right₀ (by norm_num) hm
    _ = ((2 ^ j : ℕ) : ℝ) * 2 ^ c := by
      push_cast; rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm, hj']
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hge

theorem abs_roundR_le_two_zpow (fmt : Format) (rm : RoundingDirection) {k : ℤ} {z : ℝ}
    (hk : fmt.minQ ≤ k) (hz : |z| < (2 : ℝ) ^ k) : |roundR fmt rm z| ≤ (2 : ℝ) ^ k := by
  by_cases hz0 : z = 0
  · rw [hz0, roundR_zero, abs_zero]; positivity
  have hlog := log_abs_lt_of_lt hz0 hz
  set c := cexpR fmt z with hc
  have hck : c ≤ k := by rw [hc]; unfold cexpR magR; omega
  set j := (k - c).toNat with hj
  have hj' : c + (j : ℤ) = k := by rw [hj]; omega
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have hce : ⌈|z| / 2 ^ c⌉ ≤ ((2 ^ j : ℕ) : ℤ) := by
    rw [Int.ceil_le, div_le_iff₀ hp]
    push_cast
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm, hj']
    exact hz.le
  have hle : roundAbs rm (decide (z < 0)) (|z| / 2 ^ c) ≤ ((2 ^ j : ℕ) : ℤ) :=
    le_trans (roundAbs_le_ceil _ _ _) hce
  rw [abs_roundR_eq, ← hc]
  calc _ ≤ ((2 ^ j : ℕ) : ℝ) * 2 ^ c := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        exact_mod_cast hle
    _ = 2 ^ k := by
      push_cast; rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, add_comm, hj']

theorem two_zpow_emax_le_maxFinite (fmt : Format) : (2 : ℝ) ^ emax fmt ≤ maxFinite fmt := by
  unfold maxFinite
  have h1 : (2 : ℝ) ^ (1 - (fmt.sigBits : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀ (by norm_num)
    have := fmt.sigBits_three_le; omega
  have : (0 : ℝ) < 2 ^ emax fmt := by positivity
  nlinarith

theorem maxFinite_lt_two_zpow (fmt : Format) : maxFinite fmt < (2 : ℝ) ^ (emax fmt + 1) := by
  unfold maxFinite
  have : (0 : ℝ) < 2 ^ (1 - (fmt.sigBits : ℤ)) := by positivity
  rw [zpow_add_one₀ two_ne_zero]
  have : (0 : ℝ) < 2 ^ emax fmt := by positivity
  nlinarith

theorem one_le_emax (fmt : Format) : 1 ≤ emax fmt := by
  have := one_le_bias fmt; unfold emax; omega

theorem minQ_le_emin (fmt : Format) : fmt.minQ ≤ emin fmt := by
  have := minQ_add_fracBits fmt; omega

theorem abs_lt_of_tiny {sp : Specialization} {fmt : Format} {rm : RoundingDirection} {x : ℝ}
    (h : Tiny sp fmt rm x) : |x| < (2 : ℝ) ^ emin fmt := by
  obtain ⟨_, ht⟩ := h
  cases hc : sp.tininess with
  | afterRounding =>
    rw [hc] at ht
    by_contra hn
    exact absurd ht (not_lt.2 (two_zpow_le_abs_roundRInf fmt rm (not_lt.1 hn)))
  | beforeRounding => rw [hc] at ht; exact ht

theorem sameAtScale_one_roundMagToOdd {u : ℝ} :
    SameAtScale 1 u ((roundMagToOdd u : ℤ) : ℝ) := by
  have hk := roundMagToOdd_eq u
  have hc1 := ceil_le_floor_add_one u
  have hc0 : ⌊u⌋ ≤ ⌈u⌉ := Int.floor_le_ceil u
  intro n
  have e2 : (n : ℝ) * 2 ^ (1 : ℤ) = ((2 * n : ℤ) : ℝ) := by push_cast; ring
  rw [e2, Int.cast_le, Int.cast_le, ← Int.le_floor, ← Int.ceil_le]
  set k := roundMagToOdd u
  split_ifs at hk <;> constructor <;> constructor <;> intro h <;> omega

theorem SameAtScale.mul_zpow {e c : ℤ} {a b : ℝ} (h : SameAtScale e a b) :
    SameAtScale (e + c) (a * 2 ^ c) (b * 2 ^ c) := by
  intro n
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have e1 : (n : ℝ) * 2 ^ (e + c) = (n * 2 ^ e) * 2 ^ c := by
    rw [zpow_add₀ two_ne_zero]; ring
  rw [e1, mul_le_mul_iff_left₀ hp, mul_le_mul_iff_left₀ hp, mul_le_mul_iff_left₀ hp,
    mul_le_mul_iff_left₀ hp]
  exact h n

theorem sameAtScale_roundToOdd (fmt : Format) (x : ℝ) :
    SameAtScale (cexpR fmt x + 1) x (roundR fmt .roundToOdd x) := by
  set c := cexpR fmt x with hc
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have h1 := (sameAtScale_one_roundMagToOdd (u := |x| / 2 ^ c)).mul_zpow (c := c)
  rw [div_mul_cancel₀ _ hp.ne', show (1 : ℤ) + c = c + 1 by ring] at h1
  have hy : roundR fmt .roundToOdd x
      = (if x < 0 then -1 else 1) * (((roundMagToOdd (|x| / 2 ^ c) : ℤ) : ℝ) * 2 ^ c) := by
    unfold roundR roundAbs; rw [← hc]; ring
  have hx : x = (if x < 0 then -1 else 1) * |x| := by
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  rw [hy]
  conv_lhs => rw [hx]
  split_ifs
  · simp only [neg_one_mul]; exact h1.neg
  · simp only [one_mul]; exact h1

theorem roundR_roundToOdd_ne_zero (fmt : Format) {x : ℝ} (hx0 : x ≠ 0) :
    roundR fmt .roundToOdd x ≠ 0 :=
  fun h => hx0 ((sameAtScale_roundToOdd fmt x).zero_iff.2 h)

theorem roundR_roundToOdd_neg_iff (fmt : Format) (x : ℝ) :
    roundR fmt .roundToOdd x < 0 ↔ x < 0 :=
  (sameAtScale_roundToOdd fmt x).neg_iff.symm

theorem roundedResultOf_roundToOdd_iff (sp : Specialization) {mid dst : Format}
    (h1 : dst.sigBits + 2 ≤ mid.sigBits) (h2 : mid.minQ + dst.sigBits + 2 ≤ dst.minQ)
    (rm : RoundingDirection) {x : ℝ} (hx0 : x ≠ 0) (zn : Bool) (r : ℕ × StatusFlags) :
    RoundedResultOf sp dst rm (roundR mid .roundToOdd x) zn r ↔ RoundedResultOf sp dst rm x zn r := by
  have hS := sameAtScale_roundToOdd mid x
  have hp3 := dst.sigBits_three_le
  have hm3 := mid.sigBits_three_le
  by_cases hb : (2 : ℝ) ^ (dst.minQ - 1) ≤ |x|
  · have hm := two_zpow_log_le hx0
    have hx : (2 : ℝ) ^ ((cexpR mid x + 1) + dst.sigBits) ≤ |x| := by
      by_cases hcm : mid.minQ ≤ magR x - mid.sigBits
      · have hce : cexpR mid x = magR x - mid.sigBits := by unfold cexpR; omega
        refine le_trans (zpow_le_zpow_right₀ (by norm_num) ?_) hm
        omega
      · have hce : cexpR mid x = mid.minQ := by unfold cexpR; omega
        refine le_trans (zpow_le_zpow_right₀ (by norm_num) ?_) hb
        omega
    exact (hS.roundedResultOf_iff sp dst rm zn r hx).symm
  · have hlt : |x| < (2 : ℝ) ^ (dst.minQ - 1) := not_le.1 hb
    have hlog := log_abs_lt_of_lt hx0 hlt
    have hec : cexpR mid x + 1 ≤ dst.minQ - 1 := by unfold cexpR magR; omega
    have hy : |roundR mid .roundToOdd x| < (2 : ℝ) ^ (dst.minQ - 1) := by
      have := hS.abs.lt_iff' hec (1 : ℤ)
      simp only [Int.cast_one, one_mul] at this
      exact this.1 hlt
    exact roundedResultOf_iff_of_abs_lt sp dst rm zn r (roundR_roundToOdd_ne_zero mid hx0) hx0
      (roundR_roundToOdd_neg_iff mid x) hy hlt

theorem roundedResultOf_zn_iff {sp : Specialization} {fmt : Format} {rm : RoundingDirection} {x : ℝ}
    (hx0 : x ≠ 0) (zn zn' : Bool) (r : ℕ × StatusFlags) :
    RoundedResultOf sp fmt rm x zn r ↔ RoundedResultOf sp fmt rm x zn' r := by
  unfold RoundedResultOf; simp only [hx0, ↓reduceIte]

theorem roundR_roundToOdd_eq_self {mid dst : Format}
    (h1 : dst.sigBits + 2 ≤ mid.sigBits) (h2 : mid.minQ + dst.sigBits + 2 ≤ dst.minQ)
    (rm : RoundingDirection) {x : ℝ} (h : roundR dst rm x = x) : roundR mid .roundToOdd x = x := by
  have hS := sameAtScale_roundToOdd mid x
  obtain ⟨n, hn⟩ := SameAtScale.roundR_eq_intCast_mul dst rm x
  have hec : cexpR mid x + 1 ≤ cexpR dst x := by unfold cexpR; omega
  rw [h] at hn
  rw [(hS.eq_iff' hec n).1 hn]; exact hn.symm

theorem tiny_of_tiny_wider {sp : Specialization} {mid dst : Format} (h3 : emax dst < emax mid)
    {rm rm' : RoundingDirection} {x : ℝ} (h : Tiny sp mid rm x) : Tiny sp dst rm' x := by
  have hx := abs_lt_of_tiny h
  have hx0 := h.1
  have hlt : (2 : ℝ) ^ emin mid < 2 ^ emin dst :=
    zpow_lt_zpow_right₀ (by norm_num) (by unfold emin; omega)
  refine ⟨hx0, ?_⟩
  cases hc : sp.tininess with
  | afterRounding =>
    have hlog := log_abs_lt_of_lt hx0 hx
    have hm : magR x ≤ emin mid := by unfold magR; omega
    calc |roundRInf dst rm' x| ≤ 2 ^ magR x := abs_roundRInf_le dst rm' x
      _ ≤ 2 ^ emin mid := zpow_le_zpow_right₀ (by norm_num) hm
      _ < _ := hlt
  | beforeRounding => exact lt_trans hx hlt

theorem roundedResultOf_two_step (sp : Specialization) {mid dst : Format}
    (h1 : dst.sigBits + 2 ≤ mid.sigBits) (h2 : mid.minQ + dst.sigBits + 2 ≤ dst.minQ)
    (h3 : emax dst < emax mid) (rm : RoundingDirection) {x : ℝ} (hx0 : x ≠ 0) {zn zn' : Bool}
    {s t : ℕ × StatusFlags} (hs : RoundedResultOf sp mid .roundToOdd x zn s)
    (ht : RoundedResultOf sp dst rm (valR mid s.1) zn' t) :
    RoundedResultOf sp dst rm x zn (t.1, s.2.union t.2) := by
  obtain ⟨_, hsI, hsD, hsR⟩ := hs
  have hmaxle : (2 : ℝ) ^ (emax dst + 1) ≤ maxFinite mid :=
    le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) (two_zpow_emax_le_maxFinite mid)
  have hqd : dst.minQ ≤ emax dst + 1 := by
    have := minQ_le_emin dst; have := one_le_emax dst; unfold emin at *; omega
  have hqm : mid.minQ ≤ emax dst + 1 := by
    have := minQ_le_emin mid; have := one_le_emax mid; have := one_le_emax dst; unfold emin at *; omega
  have hmp := maxFinite_pos mid
  by_cases hov : maxFinite mid < |roundR mid .roundToOdd x|
  · simp only [hov, ↓reduceIte] at hsR
    have hoti : overflowToInfinity .roundToOdd (decide (x < 0)) = false := rfl
    rw [hoti] at hsR
    simp only [Bool.false_eq_true, ↓reduceIte] at hsR
    obtain ⟨⟨_, hval⟩, hso, hsi, hsu⟩ := hsR
    have habs : |valR mid s.1| = maxFinite mid := by
      rw [hval]; split_ifs <;> simp [abs_of_pos hmp]
    have hneg : valR mid s.1 < 0 ↔ x < 0 := by
      rw [hval]; split_ifs with h
      · exact ⟨fun _ => h, fun _ => by linarith⟩
      · exact ⟨fun h' => absurd h' (not_lt.2 hmp.le), fun h' => absurd h' h⟩
    have hovy : maxFinite dst < |roundR dst rm (valR mid s.1)| :=
      lt_of_lt_of_le (maxFinite_lt_two_zpow dst)
        (two_zpow_le_abs_roundR dst rm hqd (by rw [habs]; exact hmaxle))
    have hxbig : (2 : ℝ) ^ (emax dst + 1) ≤ |x| := by
      by_contra hn
      have := abs_roundR_le_two_zpow mid .roundToOdd hqm (not_le.1 hn)
      linarith
    have hovx : maxFinite dst < |roundR dst rm x| :=
      lt_of_lt_of_le (maxFinite_lt_two_zpow dst) (two_zpow_le_abs_roundR dst rm hqd hxbig)
    obtain ⟨htE, htI, htD, htR⟩ := ht
    simp only [hovy, ↓reduceIte] at htR
    obtain ⟨hcls, hto, hti, htu⟩ := htR
    have hd : decide (valR mid s.1 < 0) = decide (x < 0) := decide_eq_decide.2 hneg
    rw [hd] at hcls
    simp only [hneg] at hcls
    refine ⟨htE, by simp [StatusFlags.union, hsI, htI], by simp [StatusFlags.union, hsD, htD], ?_⟩
    simp only [hovx, ↓reduceIte]
    exact ⟨hcls, by simp [StatusFlags.union, hso], by simp [StatusFlags.union, hsi],
      by simp [StatusFlags.union, hsu, htu]⟩
  · simp only [hov, ↓reduceIte] at hsR
    obtain ⟨_, hval, _, hso, hsi, hsu⟩ := hsR
    rw [hval] at ht
    have ht' := (roundedResultOf_zn_iff hx0 zn' zn t).1
      ((roundedResultOf_roundToOdd_iff sp h1 h2 rm hx0 zn' t).1 ht)
    obtain ⟨htE, htI, htD, htR⟩ := ht'
    refine ⟨htE, by simp [StatusFlags.union, hsI, htI], by simp [StatusFlags.union, hsD, htD], ?_⟩
    have hex : roundR dst rm x = x → roundR mid .roundToOdd x = x :=
      roundR_roundToOdd_eq_self h1 h2 rm
    by_cases hovx : maxFinite dst < |roundR dst rm x|
    · simp only [hovx, ↓reduceIte] at htR ⊢
      obtain ⟨hcls, hto, hti, htu⟩ := htR
      have hsu' : s.2.underflow = false := by
        cases hu : s.2.underflow
        · rfl
        · exfalso
          obtain ⟨_, htiny⟩ := hsu.1 hu
          have hxa := abs_lt_of_tiny htiny
          have hlt : (2 : ℝ) ^ emin mid ≤ 2 ^ emin dst :=
            zpow_le_zpow_right₀ (by norm_num) (by unfold emin; omega)
          have hr := abs_roundR_le_two_zpow dst rm (minQ_le_emin dst) (lt_of_lt_of_le hxa hlt)
          have h4 : (2 : ℝ) ^ emin dst ≤ maxFinite dst :=
            le_trans (zpow_le_zpow_right₀ (by norm_num)
              (by have := one_le_emax dst; unfold emin; omega)) (two_zpow_emax_le_maxFinite dst)
          linarith
      exact ⟨hcls, by simp [StatusFlags.union, hto], by simp [StatusFlags.union, hti],
        by simp [StatusFlags.union, hsu', htu]⟩
    · simp only [hovx, ↓reduceIte] at htR ⊢
      obtain ⟨hfin, hval', hz, hto, hti, htu⟩ := htR
      refine ⟨hfin, hval', hz, by simp [StatusFlags.union, hso, hto], ?_, ?_⟩
      · simp only [StatusFlags.union, Bool.or_eq_true]
        rw [hsi, hti]
        exact ⟨fun h => h.elim (fun h' he => h' (hex he)) id, Or.inr⟩
      · simp only [StatusFlags.union, Bool.or_eq_true]
        rw [hsu, htu]
        constructor
        · rintro (⟨hne, htiny⟩ | h)
          · exact ⟨fun he => hne (hex he), tiny_of_tiny_wider h3 htiny⟩
          · exact h
        · exact Or.inr

theorem finite_of_roundedResultOf_roundToOdd {sp : Specialization} {mid : Format} {x : ℝ}
    (hx0 : x ≠ 0) {zn : Bool} {s : ℕ × StatusFlags}
    (hs : RoundedResultOf sp mid .roundToOdd x zn s) : IsFinite mid s.1 ∧ valR mid s.1 ≠ 0 := by
  obtain ⟨_, _, _, hR⟩ := hs
  by_cases hov : maxFinite mid < |roundR mid .roundToOdd x|
  · have hoti : overflowToInfinity .roundToOdd (decide (x < 0)) = false := rfl
    simp only [hov, hoti, Bool.false_eq_true, ↓reduceIte] at hR
    obtain ⟨⟨hf, hv⟩, _⟩ := hR
    refine ⟨hf, ?_⟩
    have := maxFinite_pos mid
    rw [hv]; split_ifs <;> intro h <;> linarith
  · simp only [hov, ↓reduceIte] at hR
    obtain ⟨hf, hv, _⟩ := hR
    exact ⟨hf, hv ▸ roundR_roundToOdd_ne_zero mid hx0⟩

theorem convertFormatSpecOf_roundedResultOf {sp : Specialization} {fmt dst : Format}
    {rm : RoundingDirection} {b : ℕ} {t : ℕ × StatusFlags} (hf : IsFinite fmt b) (hv : valR fmt b ≠ 0)
    (h : ConvertFormatSpecOf sp fmt dst rm b t) : ∃ zn, RoundedResultOf sp dst rm (valR fmt b) zn t := by
  unfold ConvertFormatSpecOf at h
  unfold IsFinite at hf
  cases hc : classify fmt b with
  | quietNaN => simp [hc] at hf
  | signalingNaN => simp [hc] at hf
  | infinity _ => simp [hc] at hf
  | normal _ => simp only [hc] at h; exact ⟨_, h⟩
  | subnormal _ => simp only [hc] at h; exact ⟨_, h⟩
  | zero sg => exact absurd ((valR_eq_zero_iff fmt b).2 (Or.inr ⟨sg, hc⟩)) hv

theorem convertFormatSpecOf_two_step {sp : Specialization} {src mid dst : Format}
    (h1 : dst.sigBits + 2 ≤ mid.sigBits) (h2 : mid.minQ + dst.sigBits + 2 ≤ dst.minQ)
    (h3 : emax dst < emax mid) {rm : RoundingDirection} {a : ℕ} {s t : ℕ × StatusFlags}
    (hna : classify src a ≠ .quietNaN) (hns : classify src a ≠ .signalingNaN)
    (hs : ConvertFormatSpecOf sp src mid .roundToOdd a s) (ht : ConvertFormatSpecOf sp mid dst rm s.1 t) :
    ConvertFormatSpecOf sp src dst rm a (t.1, s.2.union t.2) := by
  unfold ConvertFormatSpecOf at hs ⊢
  have hnz : (∀ sg, classify src a ≠ .zero sg) → IsFinite src a → valR src a ≠ 0 := by
    intro hz hf h
    rcases (valR_eq_zero_iff src a).1 h with hnf | ⟨s', hs'⟩
    · exact hnf hf
    · exact hz s' hs'
  cases hc : classify src a with
  | quietNaN => exact absurd hc hna
  | signalingNaN => exact absurd hc hns
  | infinity sg =>
    simp only [hc] at hs ⊢
    obtain ⟨_, hsc, hs2⟩ := hs
    unfold ConvertFormatSpecOf at ht
    rw [hsc] at ht
    obtain ⟨htE, htc, ht2⟩ := ht
    exact ⟨htE, htc, by rw [hs2, ht2]; rfl⟩
  | zero sg =>
    simp only [hc] at hs ⊢
    have hv : valR src a = 0 := (valR_eq_zero_iff src a).2 (Or.inr ⟨sg, hc⟩)
    rw [hv] at hs ⊢
    obtain ⟨_, hsI, hsD, hsR⟩ := hs
    have hn0 : ∀ fmt : Format, ¬ (maxFinite fmt < |(0 : ℝ)|) := fun fmt => by
      rw [abs_zero]; exact not_lt.2 (maxFinite_pos fmt).le
    rw [roundR_zero] at hsR
    simp only [hn0, ↓reduceIte] at hsR
    obtain ⟨_, _, hz, hso, hsi, hsu⟩ := hsR
    have hcls : classify mid s.1 = .zero sg := by simpa using hz
    unfold ConvertFormatSpecOf at ht
    rw [hcls] at ht
    have hv1 : valR mid s.1 = 0 := (valR_eq_zero_iff mid s.1).2 (Or.inr ⟨sg, hcls⟩)
    rw [hv1] at ht
    have hsi' : s.2.inexact = false := by simpa using hsi
    have hsu' : s.2.underflow = false := by simpa using hsu
    obtain ⟨htE, htI, htD, htR⟩ := ht
    refine ⟨htE, by simp [StatusFlags.union, hsI, htI], by simp [StatusFlags.union, hsD, htD], ?_⟩
    rw [roundR_zero] at htR ⊢
    simp only [hn0, ↓reduceIte] at htR ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := htR
    refine ⟨a1, a2, a3, by simp [StatusFlags.union, hso, a4], ?_, ?_⟩
    · simp only [StatusFlags.union, hsi', Bool.false_or]; exact a5
    · simp only [StatusFlags.union, hsu', Bool.false_or]; exact a6
  | normal sg =>
    simp only [hc] at hs ⊢
    have hx0 := hnz (fun _ h => by rw [hc] at h; cases h) (by simp [IsFinite, hc])
    obtain ⟨hf, hv⟩ := finite_of_roundedResultOf_roundToOdd hx0 hs
    obtain ⟨_, ht'⟩ := convertFormatSpecOf_roundedResultOf hf hv ht
    exact roundedResultOf_two_step sp h1 h2 h3 rm hx0 hs ht'
  | subnormal sg =>
    simp only [hc] at hs ⊢
    have hx0 := hnz (fun _ h => by rw [hc] at h; cases h) (by simp [IsFinite, hc])
    obtain ⟨hf, hv⟩ := finite_of_roundedResultOf_roundToOdd hx0 hs
    obtain ⟨_, ht'⟩ := convertFormatSpecOf_roundedResultOf hf hv ht
    exact roundedResultOf_two_step sp h1 h2 h3 rm hx0 hs ht'

end SoftFloat.Proof
