/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Common
import SoftFloat.Core.Proof.Remainder

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem roundAbs_of_lt_half (rm : RoundingDirection) (neg : Bool) {t : ℝ} (h0 : 0 < t)
    (h1 : t < 1 / 2) : roundAbs rm neg t = roundAbs rm neg (1 / 4) := by
  have hf : ⌊t⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨h0.le, by linarith⟩
  have hc : ⌈t⌉ = 1 := Int.ceil_eq_iff.2 ⟨by norm_num; exact h0, by norm_num; linarith⟩
  have hf' : ⌊(1 / 4 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩
  have hc' : ⌈(1 / 4 : ℝ)⌉ = 1 := Int.ceil_eq_iff.2 ⟨by norm_num, by norm_num⟩
  have h2 : ¬ (1 / 2 ≤ t) := not_le.2 h1
  cases rm <;> cases neg <;>
    simp only [roundAbs, roundMagTiesToEven, roundMagTiesToAway, roundMagDown, roundMagUp,
      roundMagToOdd_eq, hf, hc, hf', hc', Int.cast_zero, sub_zero, Bool.false_eq_true,
      ↓reduceIte] <;>
    (try split_ifs) <;> first | rfl | omega | (exfalso; linarith)

theorem roundAbs_quarter_bounds (rm : RoundingDirection) (neg : Bool) :
    0 ≤ roundAbs rm neg (1 / 4) ∧ roundAbs rm neg (1 / 4) ≤ 1 := by
  have hf' : ⌊(1 / 4 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.2 ⟨by norm_num, by norm_num⟩
  have hc' : ⌈(1 / 4 : ℝ)⌉ = 1 := Int.ceil_eq_iff.2 ⟨by norm_num, by norm_num⟩
  have h1 := floor_le_roundAbs rm neg (1 / 4)
  have h2 := roundAbs_le_ceil rm neg (1 / 4)
  rw [hf'] at h1; rw [hc'] at h2
  exact ⟨h1, h2⟩

theorem log_abs_lt_of_lt {x : ℝ} {k : ℤ} (hx0 : x ≠ 0) (hx : |x| < 2 ^ k) : Int.log 2 |x| < k :=
  (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (abs_pos.2 hx0)).mp (by exact_mod_cast hx)

theorem cexpR_of_abs_lt (fmt : Format) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 2 ^ (fmt.minQ - 1)) :
    cexpR fmt x = fmt.minQ := by
  have := log_abs_lt_of_lt hx0 hx
  unfold cexpR magR
  omega

theorem roundR_of_abs_lt (fmt : Format) (rm : RoundingDirection) {x : ℝ} (hx0 : x ≠ 0)
    (hx : |x| < 2 ^ (fmt.minQ - 1)) :
    roundR fmt rm x = (if x < 0 then -1 else 1)
      * ((roundAbs rm (decide (x < 0)) (1 / 4) : ℤ) : ℝ) * 2 ^ fmt.minQ := by
  unfold roundR
  rw [cexpR_of_abs_lt fmt hx0 hx]
  have hp : (0 : ℝ) < 2 ^ fmt.minQ := by positivity
  have ht0 : 0 < |x| / 2 ^ fmt.minQ := div_pos (abs_pos.2 hx0) hp
  have ht1 : |x| / 2 ^ fmt.minQ < 1 / 2 := by
    rw [div_lt_iff₀ hp]
    have : (2 : ℝ) ^ (fmt.minQ - 1) = 1 / 2 * 2 ^ fmt.minQ := by
      rw [zpow_sub₀ two_ne_zero, zpow_one]; ring
    linarith
  rw [roundAbs_of_lt_half rm _ ht0 ht1]

theorem roundR_ne_self_of_abs_lt (fmt : Format) (rm : RoundingDirection) {x : ℝ} (hx0 : x ≠ 0)
    (hx : |x| < 2 ^ (fmt.minQ - 1)) : roundR fmt rm x ≠ x := by
  rw [roundR_of_abs_lt fmt rm hx0 hx]
  intro h
  obtain ⟨hc0, hc1⟩ := roundAbs_quarter_bounds rm (decide (x < 0))
  have hp : (0 : ℝ) < 2 ^ fmt.minQ := by positivity
  have hhalf : (2 : ℝ) ^ (fmt.minQ - 1) < 2 ^ fmt.minQ :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have habs : |x| = ((roundAbs rm (decide (x < 0)) (1 / 4) : ℤ) : ℝ) * 2 ^ fmt.minQ := by
    conv_lhs => rw [← h]
    rw [abs_mul, abs_mul, abs_of_pos hp]
    have : |(if x < 0 then -1 else 1 : ℝ)| = 1 := by split_ifs <;> norm_num
    rw [this, one_mul, abs_of_nonneg (by exact_mod_cast hc0)]
  rcases (show roundAbs rm (decide (x < 0)) (1 / 4) = 0 ∨ roundAbs rm (decide (x < 0)) (1 / 4) = 1
    by omega) with hc | hc <;> rw [hc] at habs <;> push_cast at habs
  · exact hx0 (abs_eq_zero.1 (by linarith))
  · linarith

theorem abs_roundRInf_le (fmt : Format) (rm : RoundingDirection) (x : ℝ) :
    |roundRInf fmt rm x| ≤ 2 ^ magR x := by
  unfold roundRInf cexpRInf
  set c := magR x - (fmt.sigBits : ℤ)
  have hp : (0 : ℝ) < 2 ^ c := by positivity
  have hlt : |x| < 2 ^ magR x := by
    unfold magR
    exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|
  have hy0 : 0 ≤ |x| / 2 ^ c := div_nonneg (abs_nonneg x) hp.le
  have hy1 : |x| / 2 ^ c ≤ ((2 ^ fmt.sigBits : ℕ) : ℤ) := by
    rw [div_le_iff₀ hp]
    push_cast
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
    have : (fmt.sigBits : ℤ) + c = magR x := by omega
    rw [this]; exact hlt.le
  have h1 := floor_le_roundAbs rm (decide (x < 0)) (|x| / 2 ^ c)
  have h2 := roundAbs_le_ceil rm (decide (x < 0)) (|x| / 2 ^ c)
  have hf : 0 ≤ ⌊|x| / 2 ^ c⌋ := Int.floor_nonneg.2 hy0
  have hc : ⌈|x| / 2 ^ c⌉ ≤ ((2 ^ fmt.sigBits : ℕ) : ℤ) := Int.ceil_le.2 hy1
  set k := roundAbs rm (decide (x < 0)) (|x| / 2 ^ c)
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast le_trans hf h1
  have hk1 : (k : ℝ) ≤ 2 ^ fmt.sigBits := by
    have : k ≤ ((2 ^ fmt.sigBits : ℕ) : ℤ) := le_trans h2 hc
    exact_mod_cast this
  rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_nonneg hk0]
  have : |(if x < 0 then -1 else 1 : ℝ)| = 1 := by split_ifs <;> norm_num
  rw [this, one_mul]
  calc (k : ℝ) * 2 ^ c ≤ 2 ^ fmt.sigBits * 2 ^ c := mul_le_mul_of_nonneg_right hk1 hp.le
    _ = 2 ^ magR x := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; omega

theorem tiny_of_abs_lt (sp : Specialization) (fmt : Format) (rm : RoundingDirection) {x : ℝ}
    (hx0 : x ≠ 0) (hx : |x| < 2 ^ (fmt.minQ - 1)) : Tiny sp fmt rm x := by
  have he : fmt.minQ - 1 < emin fmt := by
    have := minQ_add_fracBits fmt; have := one_le_fracBits fmt; omega
  have hlt : (2 : ℝ) ^ (fmt.minQ - 1) < 2 ^ emin fmt := zpow_lt_zpow_right₀ (by norm_num) he
  refine ⟨hx0, ?_⟩
  cases sp.tininess with
  | beforeRounding => exact lt_trans hx hlt
  | afterRounding =>
    have hm : magR x ≤ fmt.minQ - 1 := by have := log_abs_lt_of_lt hx0 hx; unfold magR; omega
    calc |roundRInf fmt rm x| ≤ 2 ^ magR x := abs_roundRInf_le fmt rm x
      _ ≤ 2 ^ (fmt.minQ - 1) := zpow_le_zpow_right₀ (by norm_num) hm
      _ < _ := hlt

theorem roundedResultOf_iff_of_abs_lt (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    {x y : ℝ} (zn : Bool) (r : ℕ × StatusFlags) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hn : x < 0 ↔ y < 0)
    (hx : |x| < 2 ^ (fmt.minQ - 1)) (hy : |y| < 2 ^ (fmt.minQ - 1)) :
    RoundedResultOf sp fmt rm x zn r ↔ RoundedResultOf sp fmt rm y zn r := by
  have hd : decide (x < 0) = decide (y < 0) := by simp [hn]
  have hR : roundR fmt rm x = roundR fmt rm y := by
    rw [roundR_of_abs_lt fmt rm hx0 hx, roundR_of_abs_lt fmt rm hy0 hy, hd]
    simp only [hn]
  have hE : roundR fmt rm y ≠ x ↔ roundR fmt rm y ≠ y :=
    ⟨fun _ => roundR_ne_self_of_abs_lt fmt rm hy0 hy,
      fun _ => hR ▸ roundR_ne_self_of_abs_lt fmt rm hx0 hx⟩
  have hT : Tiny sp fmt rm x ↔ Tiny sp fmt rm y :=
    ⟨fun _ => tiny_of_abs_lt sp fmt rm hy0 hy, fun _ => tiny_of_abs_lt sp fmt rm hx0 hx⟩
  have hz : x = 0 ↔ y = 0 := ⟨fun h => absurd h hx0, fun h => absurd h hy0⟩
  unfold RoundedResultOf
  rw [hR]
  simp only [hn, hz, hE, hT]

theorem exponentOfU_bounds (fmt : Format) {x : Nat} (hf : IsFinite fmt x)
    (hz : isZeroU (fmt.unpack x) = false) :
    1 - (fmt.bias : ℤ) - fmt.fracBits ≤ fmt.exponentOfU (fmt.unpack x)
      ∧ fmt.exponentOfU (fmt.unpack x) ≤ fmt.bias := by
  have h1 := minQ_le_ulpExpOf fmt (fmt.unpack x)
  have h2 := ulpExpOf_add_fracBits_le_emax fmt hf
  have hm := sigOf_lt_two_pow_sigBits fmt (fmt.unpack x) (unpack_fracField_lt fmt x)
  have hl := (Nat.log2_lt (sigOf_pos fmt hz).ne').2 hm
  have hs := sigBits_eq_fracBits_add_one fmt
  unfold Format.exponentOfU
  unfold Format.minQ at h1; unfold emax at h2
  omega

theorem logBExponent_eq (fmt : Format) {x : Nat} (hf : IsFinite fmt x)
    (hz : isZeroU (fmt.unpack x) = false) :
    logBExponent fmt x = fmt.exponentOfU (fmt.unpack x) := by
  have := magR_signed (fmt.unpack x).sign _ (fmt.ulpExpOf (fmt.unpack x)) (sigOf_pos fmt hz)
  unfold magR topExp at this
  unfold logBExponent Format.exponentOfU
  rw [valR_eq_sigOf fmt hf]
  push_cast at this
  omega

theorem two_pow_eq_two_mul (w : Nat) (hw : 0 < w) : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
  rw [← pow_succ']; congr 1; omega

theorem isTwosComplementOf_ofTwosComplement {w n : Nat} (hw : 0 < w) (hn : n < 2 ^ w) :
    IsTwosComplementOf w n (Format.ofTwosComplement w n) := by
  have hM := two_pow_eq_two_mul w hw
  have hn' : (n : ℤ) < 2 ^ w := by exact_mod_cast hn
  unfold IsTwosComplementOf Format.ofTwosComplement intRangeLo intRangeHi
  simp only [↓reduceIte]
  split_ifs with h
  · have h' : (n : ℤ) < 2 ^ (w - 1) := by exact_mod_cast h
    refine ⟨by have : (0 : ℤ) < 2 ^ (w - 1) := by positivity
               omega, by omega, ?_⟩
    rw [Int.emod_eq_of_lt (by positivity) hn']; rfl
  · have h' : ¬ (n : ℤ) < 2 ^ (w - 1) := by exact_mod_cast h
    refine ⟨by omega, by omega, ?_⟩
    rw [show (n : ℤ) - 2 ^ w = n + (-1) * 2 ^ w by ring, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by positivity) hn']
    rfl

theorem eq_of_isTwosComplementOf {w n : Nat} {N N' : ℤ} (hw : 0 < w) (h : IsTwosComplementOf w n N)
    (h' : IsTwosComplementOf w n N') : N = N' := by
  obtain ⟨hl, hh, he⟩ := h
  obtain ⟨hl', hh', he'⟩ := h'
  unfold intRangeLo at hl hl'; unfold intRangeHi at hh hh'
  simp only [↓reduceIte] at hl hl' hh hh'
  have hM := two_pow_eq_two_mul w hw
  have hpos : (0 : ℤ) < 2 ^ w := by positivity
  have hmod : N % 2 ^ w = N' % 2 ^ w := by
    have h1 := Int.emod_nonneg N hpos.ne'
    have h2 := Int.emod_nonneg N' hpos.ne'
    have := he.trans he'.symm
    omega
  have hd : (2 : ℤ) ^ w ∣ N' - N := Int.ModEq.dvd hmod
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
  omega

theorem ofTwosComplement_eq {w n : Nat} {N : ℤ} (hw : 0 < w) (hn : n < 2 ^ w)
    (h : IsTwosComplementOf w n N) : Format.ofTwosComplement w n = N :=
  eq_of_isTwosComplementOf hw (isTwosComplementOf_ofTwosComplement hw hn) h

theorem integralValueU_eq {fmt : Format} {n : Nat} {N : ℤ} (hf : IsFinite fmt n)
    (hN : valR fmt n = N) : fmt.integralValueU (fmt.unpack n) = N := by
  have hv := valR_eq_sigOf fmt hf
  set m := fmt.sigOf (fmt.unpack n)
  set q := fmt.ulpExpOf (fmt.unpack n)
  set s := (fmt.unpack n).sign
  have hz : ∀ z : ℕ, (z : ℝ) = m * 2 ^ q →
      ((if s then -(z : ℤ) else (z : ℤ) : ℤ) : ℝ) = valR fmt n := by
    intro z hz
    rw [hv, mul_assoc, ← hz]
    cases s <;> simp
  have key : ((fmt.integralValueU (fmt.unpack n) : ℤ) : ℝ) = valR fmt n := by
    unfold Format.integralValueU
    simp only
    apply hz
    split_ifs with hq
    · rw [Nat.shiftLeft_eq]; push_cast
      rw [← zpow_natCast, Int.toNat_of_nonneg hq]
    · rw [Nat.shiftRight_eq_div_pow]
      set k := (-q).toNat
      have hk : (k : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      have habs : (m : ℝ) * 2 ^ q = (N.natAbs : ℝ) := by
        have h1 : |valR fmt n| = (m : ℝ) * 2 ^ q := by
          rw [hv, mul_assoc]; exact abs_sign_mul s _ (by positivity)
        rw [← h1, hN, Nat.cast_natAbs, Int.cast_abs]
      have hmk : m = N.natAbs * 2 ^ k := by
        have : (m : ℝ) = (N.natAbs : ℝ) * 2 ^ k := by
          rw [← habs, mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero, hk, add_neg_cancel,
            zpow_zero, mul_one]
        exact_mod_cast this
      change ((m / 2 ^ k : ℕ) : ℝ) = _
      rw [hmk, Nat.mul_div_cancel _ (Nat.two_pow_pos k), ← habs, hmk]
  exact_mod_cast key.trans hN

theorem isZeroU_eq_false_of_classify (fmt : Format) {x : Nat} {t : Bool}
    (hc : classify fmt x = .normal t ∨ classify fmt x = .subnormal t) :
    isZeroU (fmt.unpack x) = false := by
  rcases hc with hc | hc
  · obtain ⟨hn, -⟩ := (classify_eq_normal_iff fmt x t).1 hc
    unfold Format.isNormalU at hn; unfold Format.isZeroU
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.1]
  · obtain ⟨hn, -⟩ := (classify_eq_subnormal_iff fmt x t).1 hc
    unfold Format.isSubnormalU at hn; unfold Format.isZeroU
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hn; simp [hn.2]

theorem logB_sourceFormat_finite_spec (sp : Specialization) (fmt : Format) {x : Nat}
    (hv : LogBFormat.Valid fmt .sourceFormat) (hf : IsFinite fmt x)
    (hz : isZeroU (fmt.unpack x) = false) :
    (fmt.convertFromInt sp .roundTiesToEven (fmt.exponentOfU (fmt.unpack x))).1 < 2 ^ fmt.width
    ∧ IsFinite fmt (fmt.convertFromInt sp .roundTiesToEven (fmt.exponentOfU (fmt.unpack x))).1
    ∧ valR fmt (fmt.convertFromInt sp .roundTiesToEven (fmt.exponentOfU (fmt.unpack x))).1
      = logBExponent fmt x
    ∧ (logBExponent fmt x = 0 →
      classify fmt (fmt.convertFromInt sp .roundTiesToEven (fmt.exponentOfU (fmt.unpack x))).1
        = .zero false) := by
  rw [logBExponent_eq fmt hf hz]
  obtain ⟨hlo, hhi⟩ := exponentOfU_bounds fmt hf hz
  set e := fmt.exponentOfU (fmt.unpack x)
  have h0 : (0 : Nat) < fmt.expMax := Nat.pos_of_ne_zero (expMax_ne_zero fmt)
  unfold Format.convertFromInt
  split_ifs with he
  · rw [he]
    exact ⟨pack_zero_lt fmt false, isFinite_pack fmt false h0 (by positivity),
      by rw [valR_pack_zero]; simp, fun _ => classify_pack_zero fmt false⟩
  · have hV : 2 * ((fmt.bias : ℤ) + fmt.sigBits) ≤ ((2 ^ fmt.sigBits : ℕ) : ℤ) := by
      have := hv; unfold LogBFormat.Valid logBRange emax at this; exact_mod_cast this
    have hs := sigBits_eq_fracBits_add_one fmt
    have hb := one_le_bias fmt
    have hm : e.natAbs < 2 ^ fmt.sigBits := by
      have : (e.natAbs : ℤ) < ((2 ^ fmt.sigBits : ℕ) : ℤ) := by omega
      exact_mod_cast this
    have hq : fmt.minQ ≤ 0 := by unfold Format.minQ; omega
    have hq' : (0 : ℤ) + fmt.fracBits ≤ emax fmt := by
      have := fmt.fracBits_le_bias; unfold emax; omega
    obtain ⟨hw, hfin, hval, -⟩ :=
      roundPack_exact_spec sp fmt .roundTiesToEven (decide (e < 0)) (Int.natAbs_pos.2 he) hm hq hq'
    refine ⟨hw, hfin, ?_, fun h => absurd h he⟩
    rw [hval, zpow_zero, mul_one, ← intCast_eq_signed_natAbs]

theorem logB_spec (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format)
    (lf : LogBFormat) (x : Nat) (hv : LogBFormat.Valid fmt lf) :
    LogBSpecOf sp fmt lf x (fmt.logB sp lf x) := by
  have hnan := isNaNU_unpack fmt x
  have hsnan := isSNaNU_unpack fmt x
  cases lf with
  | sourceFormat =>
    unfold LogBSpecOf Format.logB
    cases hc : classify fmt x with
    | quietNaN =>
      have h : isNaN fmt x = true := by simp [isNaN, hc]
      simp only [hnan, h, ↓reduceIte]
      exact ⟨(hsp.propagateNaN _ _ _).2, trivial, by rw [hsnan]⟩
    | signalingNaN =>
      have h : isNaN fmt x = true := by simp [isNaN, hc]
      simp only [hnan, h, ↓reduceIte]
      exact ⟨(hsp.propagateNaN _ _ _).2, trivial, by rw [hsnan]⟩
    | infinity t =>
      obtain ⟨hi, -⟩ := (classify_eq_infinity_iff fmt x t).1 hc
      have h : isNaN fmt x = false := by simp [isNaN, hc]
      simp only [hnan, h, hi, Bool.false_eq_true, ↓reduceIte]
      exact ⟨pack_expMax_lt fmt false, classify_pack_infinity fmt false, trivial⟩
    | zero t =>
      obtain ⟨hz, -⟩ := (classify_eq_zero_iff fmt x t).1 hc
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte]
      exact ⟨pack_expMax_lt fmt true, classify_pack_infinity fmt true, trivial⟩
    | normal t =>
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      have hz := isZeroU_eq_false_of_classify fmt (Or.inl hc)
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := logB_sourceFormat_finite_spec sp fmt hv hf hz
      exact ⟨h1, h2, h3, h4, trivial⟩
    | subnormal t =>
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      have hz := isZeroU_eq_false_of_classify fmt (Or.inr hc)
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4⟩ := logB_sourceFormat_finite_spec sp fmt hv hf hz
      exact ⟨h1, h2, h3, h4, trivial⟩
  | integer w nanValue infinityValue zeroValue =>
    unfold LogBSpecOf Format.logB Format.toTwosComplement
    cases hc : classify fmt x with
    | quietNaN =>
      have h : isNaN fmt x = true := by simp [isNaN, hc]
      simp only [hnan, h, ↓reduceIte]
    | signalingNaN =>
      have h : isNaN fmt x = true := by simp [isNaN, hc]
      simp only [hnan, h, ↓reduceIte]
    | infinity t =>
      obtain ⟨hi, -⟩ := (classify_eq_infinity_iff fmt x t).1 hc
      have h : isNaN fmt x = false := by simp [isNaN, hc]
      simp only [hnan, h, hi, Bool.false_eq_true, ↓reduceIte]
    | zero t =>
      obtain ⟨hz, -⟩ := (classify_eq_zero_iff fmt x t).1 hc
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte]
    | normal t =>
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      have hz := isZeroU_eq_false_of_classify fmt (Or.inl hc)
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte, logBExponent_eq fmt hf hz]
    | subnormal t =>
      have hf : IsFinite fmt x := by simp [IsFinite, hc]
      have hz := isZeroU_eq_false_of_classify fmt (Or.inr hc)
      simp only [isNaNU_eq_false_of_isFinite fmt hf, isInfU_eq_false_of_isFinite fmt hf, hz,
        Bool.false_eq_true, ↓reduceIte, logBExponent_eq fmt hf hz]

theorem softfloat_logB_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt lf x, LogBFormat.Valid fmt lf → x < 2 ^ fmt.width →
      LogBSpecOf sp fmt lf x ((softfloat sp).logB fmt lf x) :=
  fun fmt lf x hv _ => logB_spec sp hsp fmt lf x hv

theorem roundedResultOf_scaleB_finite (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    {x : Nat} (hf : IsFinite fmt x) (hz : isZeroU (fmt.unpack x) = false) (N : ℤ) :
    RoundedResultOf sp fmt rm (valR fmt x * 2 ^ N) (fmt.unpack x).sign
      (fmt.roundPack sp rm (fmt.unpack x).sign (fmt.sigOf (fmt.unpack x))
        (fmt.ulpExpOf (fmt.unpack x) + Max.max N (-fmt.scaleBLimit))) := by
  set s := (fmt.unpack x).sign
  set m := fmt.sigOf (fmt.unpack x)
  set q := fmt.ulpExpOf (fmt.unpack x)
  have hm0 : 0 < m := sigOf_pos fmt hz
  have heq : valR fmt x * 2 ^ N = (if s then -1 else 1) * (m : ℝ) * 2 ^ (q + N) := by
    rw [valR_eq_sigOf fmt hf, zpow_add₀ two_ne_zero]; ring
  rw [heq]
  by_cases hN : -fmt.scaleBLimit ≤ N
  · rw [max_eq_left hN]
    exact roundPack_spec sp fmt rm s m (q + N) hm0 s
  · rw [max_eq_right (le_of_lt (not_le.1 hN))]
    have hq := ulpExpOf_add_fracBits_le_emax fmt hf
    have hml := sigOf_lt_two_pow_sigBits fmt (fmt.unpack x) (unpack_fracField_lt fmt x)
    have hs := sigBits_eq_fracBits_add_one fmt
    have hsmall : ∀ k : ℤ, k ≤ q + -fmt.scaleBLimit →
        |(if s then -1 else 1) * (m : ℝ) * 2 ^ k| < 2 ^ (fmt.minQ - 1) := by
      intro k hk
      rw [abs_signed]
      have hml' : (m : ℝ) < 2 ^ (fmt.sigBits : ℤ) := by
        rw [zpow_natCast]; exact_mod_cast hml
      calc (m : ℝ) * 2 ^ k < 2 ^ (fmt.sigBits : ℤ) * 2 ^ k :=
            mul_lt_mul_of_pos_right hml' (by positivity)
        _ = 2 ^ ((fmt.sigBits : ℤ) + k) := by rw [zpow_add₀ two_ne_zero]
        _ ≤ 2 ^ (fmt.minQ - 1) := by
          apply zpow_le_zpow_right₀ (by norm_num)
          unfold Format.scaleBLimit at hk; unfold emax at hq; unfold Format.minQ
          omega
    rw [roundedResultOf_iff_of_abs_lt sp fmt rm s _ (signed_ne_zero s m _ hm0)
      (signed_ne_zero s m _ hm0) ((signed_neg_iff s m _ hm0).trans (signed_neg_iff s m _ hm0).symm)
      (hsmall _ (by omega)) (hsmall _ le_rfl)]
    exact roundPack_spec sp fmt rm s m _ hm0 s

theorem scaleBNumber_spec (sp : Specialization) (fmt : Format) (rm : RoundingDirection) {x : Nat}
    (hn : isNaN fmt x = false) (N : ℤ) :
    (fmt.scaleBNumber sp rm (fmt.unpack x) N).1 < 2 ^ fmt.width
    ∧ scaleBNumberOf sp fmt rm x N (fmt.scaleBNumber sp rm (fmt.unpack x) N) := by
  unfold scaleBNumberOf Format.scaleBNumber
  cases hc : classify fmt x with
  | quietNaN => simp [isNaN, hc] at hn
  | signalingNaN => simp [isNaN, hc] at hn
  | infinity t =>
    obtain ⟨hi, hs⟩ := (classify_eq_infinity_iff fmt x t).1 hc
    simp only [hi, hs, ↓reduceIte]
    exact ⟨pack_expMax_lt fmt t, classify_pack_infinity fmt t, trivial⟩
  | zero t =>
    obtain ⟨hz, hs⟩ := (classify_eq_zero_iff fmt x t).1 hc
    have hf : IsFinite fmt x := by simp [IsFinite, hc]
    have hv : valR fmt x = 0 := (valR_eq_zero_iff fmt x).2 (Or.inr ⟨t, hc⟩)
    simp only [isInfU_eq_false_of_isFinite fmt hf, hz, hs, Bool.false_eq_true, ↓reduceIte]
    rw [hv, zero_mul]
    exact ⟨pack_zero_lt fmt t, roundedResultOf_zero sp fmt rm t⟩
  | normal t =>
    have hf : IsFinite fmt x := by simp [IsFinite, hc]
    have hz := isZeroU_eq_false_of_classify fmt (Or.inl hc)
    have hs := ((classify_eq_normal_iff fmt x t).1 hc).2
    simp only [isInfU_eq_false_of_isFinite fmt hf, hz, Bool.false_eq_true, ↓reduceIte]
    have H := roundedResultOf_scaleB_finite sp fmt rm hf hz N
    rw [← hs]
    exact ⟨H.1, H⟩
  | subnormal t =>
    have hf : IsFinite fmt x := by simp [IsFinite, hc]
    have hz := isZeroU_eq_false_of_classify fmt (Or.inr hc)
    have hs := ((classify_eq_subnormal_iff fmt x t).1 hc).2
    simp only [isInfU_eq_false_of_isFinite fmt hf, hz, Bool.false_eq_true, ↓reduceIte]
    have H := roundedResultOf_scaleB_finite sp fmt rm hf hz N
    rw [← hs]
    exact ⟨H.1, H⟩

theorem logBFormat_valid_integer_width_pos {fmt : Format} {w : Nat} {a b c : ℤ}
    (hv : LogBFormat.Valid fmt (.integer w a b c)) : 0 < w := by
  obtain ⟨-, hh, -⟩ := hv
  unfold intRangeHi logBRange emax at hh
  simp only [↓reduceIte] at hh
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · subst h0; simp at hh; have := fmt.sigBits_three_le; omega
  · exact h0

theorem scaleB_spec (sp : Specialization) (hsp : Specialization.Valid sp) (fmt : Format)
    (lf : LogBFormat) (rm : RoundingDirection) (x n : Nat) (hv : LogBFormat.Valid fmt lf)
    (hn : ScaleBOperandValid fmt lf n) :
    ScaleBSpecOf sp fmt lf rm x n (fmt.scaleB sp lf rm x n) := by
  cases lf with
  | sourceFormat =>
    unfold ScaleBSpecOf Format.scaleB
    simp only [isNaNU_unpack, isSNaNU_unpack]
    cases hx : isNaN fmt x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hnn : isNaN fmt n
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hw, H⟩ := scaleBNumber_spec sp fmt rm hx (fmt.integralValueU (fmt.unpack n))
        refine ⟨hw, fun hf N hN => ?_⟩
        rw [integralValueU_eq hf hN] at H ⊢
        exact H
      · simp only [↓reduceIte]
        exact ⟨hsp.scaleBOfNaNExponent fmt rm x n, trivial⟩
    · simp only [↓reduceIte]
      exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩
  | integer w a b c =>
    have hw0 := logBFormat_valid_integer_width_pos hv
    unfold ScaleBSpecOf Format.scaleB
    simp only [isNaNU_unpack, isSNaNU_unpack]
    by_cases h : isNaN fmt x = true
    · simp only [h, ↓reduceIte]
      exact ⟨(hsp.propagateNaN _ _ _).2, trivial, trivial⟩
    · have hx : isNaN fmt x = false := by simp_all
      simp only [hx, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hw, H⟩ := scaleBNumber_spec sp fmt rm hx (Format.ofTwosComplement w n)
      refine ⟨hw, fun N hN => ?_⟩
      rw [ofTwosComplement_eq hw0 hn hN] at H ⊢
      exact H

theorem softfloat_scaleB_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fmt lf rm x n, LogBFormat.Valid fmt lf → x < 2 ^ fmt.width → ScaleBOperandValid fmt lf n →
      ScaleBSpecOf sp fmt lf rm x n ((softfloat sp).scaleB fmt lf rm x n) :=
  fun fmt lf rm x n hv _ hn => scaleB_spec sp hsp fmt lf rm x n hv hn

theorem logBSpecOf_unique {sp : Specialization} {fmt : Format} {lf : LogBFormat} {x : Nat}
    {r₁ r₂ : Nat × StatusFlags} (h₁ : LogBSpecOf sp fmt lf x r₁) (h₂ : LogBSpecOf sp fmt lf x r₂) :
    r₁ = r₂ := by
  cases lf with
  | sourceFormat =>
    unfold LogBSpecOf at h₁ h₂
    obtain ⟨hw₁, h₁⟩ := h₁
    obtain ⟨hw₂, h₂⟩ := h₂
    cases hc : classify fmt x <;> simp only [hc] at h₁ h₂
    · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    · exact Prod.ext (eq_of_classify_eq_infinity fmt hw₁ hw₂ h₁.1 h₂.1) (h₁.2.trans h₂.2.symm)
    all_goals first
      | exact Prod.ext (eq_of_classify_eq_infinity fmt hw₁ hw₂ h₁.1 h₂.1) (h₁.2.trans h₂.2.symm)
      | (obtain ⟨hf₁, hv₁, hz₁, hfl₁⟩ := h₁
         obtain ⟨hf₂, hv₂, hz₂, hfl₂⟩ := h₂
         refine Prod.ext ?_ (hfl₁.trans hfl₂.symm)
         by_cases h0 : logBExponent fmt x = 0
         · exact eq_of_classify_eq_zero fmt hw₁ hw₂ (hz₁ h0) (hz₂ h0)
         · exact eq_of_valR_eq fmt hw₁ hw₂ hf₁ hf₂ (hv₁.trans hv₂.symm)
             (by rw [hv₁]; exact_mod_cast h0))
  | integer w a b c =>
    unfold LogBSpecOf at h₁ h₂
    cases hc : classify fmt x <;> simp only [hc] at h₁ h₂ <;> exact h₁.trans h₂.symm

theorem scaleBNumberOf_unique {sp : Specialization} {fmt : Format} {rm : RoundingDirection}
    {x : Nat} {N : ℤ} {r₁ r₂ : Nat × StatusFlags} (hw₁ : r₁.1 < 2 ^ fmt.width)
    (hw₂ : r₂.1 < 2 ^ fmt.width) (h₁ : scaleBNumberOf sp fmt rm x N r₁)
    (h₂ : scaleBNumberOf sp fmt rm x N r₂) : r₁ = r₂ := by
  unfold scaleBNumberOf at h₁ h₂
  cases hc : classify fmt x <;> simp only [hc] at h₁ h₂
  all_goals first
    | exact roundedResultOf_unique h₁ h₂
    | exact Prod.ext (eq_of_classify_eq_infinity fmt hw₁ hw₂ h₁.1 h₂.1) (h₁.2.trans h₂.2.symm)

theorem scaleBSpecOf_unique {sp : Specialization} {fmt : Format} {lf : LogBFormat}
    {rm : RoundingDirection} {x n : Nat} {r₁ r₂ : Nat × StatusFlags}
    (hv : LogBFormat.Valid fmt lf) (hn : ScaleBOperandValid fmt lf n)
    (h₁ : ScaleBSpecOf sp fmt lf rm x n r₁) (h₂ : ScaleBSpecOf sp fmt lf rm x n r₂) : r₁ = r₂ := by
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  cases lf with
  | sourceFormat =>
    simp only at h₁ h₂
    split_ifs at h₁ h₂ with h h'
    · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    · exact h₁.trans h₂.symm
    · obtain ⟨-, hn⟩ := hn
      rcases hn with hnan | ⟨hf, N, hN⟩
      · exact absurd hnan h'
      · exact scaleBNumberOf_unique hw₁ hw₂ (h₁ hf N hN) (h₂ hf N hN)
  | integer w a b c =>
    have hw0 := logBFormat_valid_integer_width_pos hv
    have hN := isTwosComplementOf_ofTwosComplement hw0 (show n < 2 ^ w from hn)
    simp only at h₁ h₂
    split_ifs at h₁ h₂
    · exact Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    · exact scaleBNumberOf_unique hw₁ hw₂ (h₁ _ hN) (h₂ _ hN)

end SoftFloat.Proof
