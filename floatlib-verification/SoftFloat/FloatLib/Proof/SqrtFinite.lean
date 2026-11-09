/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Sqrt
import SoftFloat.FloatLib.Proof.RoundRational
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics

/-!
# Square root of FloatLib against the specification of SoftFloat: positive finite operands

On a positive finite nonzero operand, the public square root of FloatLib rounds the exact real
square root once to nearest with ties to even. The result never overflows and is never zero. The
status is inexact when the delivered value is not the root, and underflows when it is inexact and
the delivered value is subnormal or the root is below `umidR`, a test that FloatLib makes on the
radicand against the square of the boundary. It meets `SquareRootSpecOf` for every
specialization with the choices of FloatLib.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

variable {fmt : Format} {a : Nat}

theorem sqrtF_umidR_pos (fmt : Format) : 0 < umidR fmt :=
  lt_of_lt_of_le (by positivity) (le_umidR fmt)

/-- FloatLib tests the square root of a nonnegative radicand against `umidR` for tininess. -/
theorem sqrtF_isTiny_iff (d : Dyadic) (hd : d.negative = false) :
    Model.dyadicSqrtIsTinyAfterRounding (toFL fmt) .nearest d = true ↔
      Real.sqrt d.toReal < umidR fmt := by
  have hsq : ({
        negative := false
        significand := (Model.underflowMidpoint (toFL fmt)).significand *
          (Model.underflowMidpoint (toFL fmt)).significand
        exponent := (Model.underflowMidpoint (toFL fmt)).exponent +
          (Model.underflowMidpoint (toFL fmt)).exponent } : Dyadic).toReal = umidR fmt ^ 2 := by
    rw [← toReal_underflowMidpoint]
    simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
      _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand, Bool.false_eq_true, ↓reduceIte,
      one_mul, Model.underflowMidpoint, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    push_cast
    ring
  have hd' : ({ d with negative := false } : Dyadic) = d := by
    cases d; cases hd; rfl
  rw [Real.sqrt_lt' (sqrtF_umidR_pos fmt)]
  unfold Model.dyadicSqrtIsTinyAfterRounding
  dsimp only
  rw [hd']
  rcases lt_trichotomy d.toReal (umidR fmt ^ 2) with h | h | h
  · rw [(Model.cmpDyadic_lt_iff _ _).mpr (by rw [hsq]; exact h)]
    simp only [true_iff]
    exact h
  · rw [(Model.cmpDyadic_eq_iff _ _).mpr (by rw [hsq]; exact h)]
    simp only [Model.IEEERoundingMode.roundsAwayFromZero, Bool.false_eq_true, false_iff, not_lt]
    exact h.ge
  · rw [(Model.cmpDyadic_gt_iff _ _).mpr (by rw [hsq]; exact h)]
    simp only [Bool.false_eq_true, false_iff, not_lt]
    exact h.le

/-- The square root of FloatLib on a positive finite nonzero operand: the rounded root and the
status of the rounding. -/
theorem flSqrt_of_toDyadic {d : Dyadic} (hx : Model.toDyadic? (ofBits fmt a) = some d)
    (hz : d.significand ≠ 0) (hs : d.negative = false) :
    flSqrt fmt a = ((Model.sqrt (ofBits fmt a) (mode := .nearest)).toNatBits,
      flagsOf {
        underflow :=
          (Model.dyadicSqrtTernary d (Model.sqrt (ofBits fmt a) (mode := .nearest)) != .eq) &&
            (Model.isTinyAfterRounding (Model.sqrt (ofBits fmt a) (mode := .nearest)) ||
              Model.dyadicSqrtIsTinyAfterRounding (toFL fmt) .nearest d)
        inexact :=
          Model.dyadicSqrtTernary d (Model.sqrt (ofBits fmt a) (mode := .nearest)) != .eq }) := by
  show ofOutcome (Model.sqrt (ofBits fmt a) (mode := .nearest) (status := true)) = _
  rw [Model.sqrt_status_of_toDyadic .nearest hx hz hs]
  rfl

/-- The square root of FloatLib meets the specification of SoftFloat when the operand is positive,
finite and nonzero. -/
theorem floatlib_sqrt_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a : Nat} (ha : a < 2 ^ fmt.width) (hx : sqrtExceptional fmt a = false) :
    SquareRootSpecOf sp fmt fmt .roundTiesToEven a (flSqrt fmt a) := by
  rw [squareRootSpecOf_of_not_exceptional sp fmt fmt _ a _ hx]
  unfold sqrtExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨hn, hz⟩, hs⟩, hi⟩ := hx
  have hF := isIEEE_toFL fmt
  have hfa : IsFinite fmt a :=
    isFinite_of_not_isNaN_not_isInfU fmt hn (by rw [← arithIsInf_eq]; exact hi)
  have hdx := toDyadic?_ofBits ha hfa
  set d := decodeU fmt (fmt.unpack a)
  have hsa : (fmt.unpack a).sign = false := by rw [← arithSign_eq fmt hn]; exact hs
  have hneg : d.negative = false := by rw [decodeU_negative]; exact hsa
  have hzx : Model.isZero (ofBits fmt a) = false := by rw [div_isZero_ofBits ha, hz]
  have hzd : d.significand ≠ 0 := by
    have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdx
    rw [hzx] at this
    intro h0
    rw [h0] at this
    cases this
  have hfx : Model.isFinite (ofBits fmt a) = true := Model.isFinite_eq_true_of_toDyadic?_some hdx
  have hsx : Model.signBit (ofBits fmt a) = false := by rw [signBit_ofBits ha]; exact hsa
  have hxv : Model.toReal (ofBits fmt a) = valR fmt a := toReal_ofBits ha hfa
  have hdv : d.toReal = valR fmt a := toReal_decodeU hfa
  -- The radicand is at least the least subnormal, and so is its root.
  have hmin : (2 : ℝ) ^ fmt.minQ ≤ valR fmt a := by
    have he := Model.minSubnormalExponent_le_toDyadic? _ hdx
    rw [minSubnormalExponent_toFL] at he
    have h1 : (1 : ℝ) ≤ d.significand := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzd
    have h2 : (2 : ℝ) ^ fmt.minQ ≤ 2 ^ d.exponent := zpow_le_zpow_right₀ (by norm_num) he
    have hd : d.toReal = (d.significand : ℝ) * 2 ^ d.exponent := by
      simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
        _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand, hneg, Bool.false_eq_true,
        ↓reduceIte, one_mul]
    rw [← hdv, hd]
    nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) d.exponent]
  have hrmin : (2 : ℝ) ^ fmt.minQ ≤ Real.sqrt (valR fmt a) := by
    apply Real.le_sqrt_of_sq_le
    have h1 : (2 : ℝ) ^ fmt.minQ ≤ 1 := by
      apply zpow_le_one_of_nonpos₀ (by norm_num)
      have := minQ_le_emax_sub fmt
      have := one_le_bias fmt
      unfold Format.minQ
      omega
    have h0 : (0 : ℝ) ≤ 2 ^ fmt.minQ := by positivity
    nlinarith
  have hr0 : 0 < Real.sqrt (valR fmt a) := lt_of_lt_of_le (by positivity) hrmin
  -- The delivered value is finite and is the rounded root.
  have hvf := Model.isFinite_sqrt_of_isFinite (ofBits fmt a) hF hfx (Or.inr hsx)
  have hvR : Model.toReal (Model.sqrt (ofBits fmt a) (mode := .nearest)) =
      roundR fmt .roundTiesToEven (Real.sqrt (valR fmt a)) := by
    rw [Model.toReal_sqrt_eq_roundAt _ hF hfx (Or.inr hsx), hxv, roundR_eq_roundAt]
  have hlt : |Real.sqrt (valR fmt a)| < midR fmt := by
    by_contra h
    have hb := Model.abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite _ hF hvf
    rw [toReal_posMaxFinite_toFL, hvR] at hb
    exact absurd ((maxFinite_lt_abs_roundR_iff fmt _).mpr (not_lt.mp h)) (not_lt.mpr hb)
  have hR0 : roundR fmt .roundTiesToEven (Real.sqrt (valR fmt a)) ≠ 0 := by
    have hpos : 0 < Model.toReal (Model.posMinSubnormal (toFL fmt)) := by
      rw [Model.toReal_posMinSubnormal]; exact Model.bpow_pos _
    have hmono := Model.roundAt_mono (toFL fmt) (x := Model.toReal (Model.posMinSubnormal (toFL fmt)))
      (y := Real.sqrt (valR fmt a)) (by
        rw [Model.toReal_posMinSubnormal, minSubnormalExponent_toFL, Model.bpow, bpow_binary]
        exact hrmin)
    rw [Model.roundAt_toReal_eq _ (Model.isFinite_posMinSubnormal _), ← roundR_eq_roundAt] at hmono
    exact (lt_of_lt_of_le hpos hmono).ne'
  -- The inexact flag.
  have hI := Model.sqrt_inexact_iff .nearest hfx hzx hsx
  rw [Model.sqrt_status_of_toDyadic .nearest hdx hzd hneg] at hI
  dsimp only at hI
  rw [hxv, hvR] at hI
  rw [flSqrt_of_toDyadic hdx hzd hneg]
  refine ⟨isEncoding_toNatBits _, ?_⟩
  apply ratF_meets sp hc.tininess hr0.ne' false _ _ ?_ rfl rfl
    (fun h => absurd h (not_le.mpr hlt))
  · intro _
    refine ⟨hvf, hvR, rfl, ?_, ?_⟩
    · show _ = true ↔ _
      rw [hI, hvR]
    · show ((_ != _) && _) = true ↔ (_ != _) = true ∧ _
      rw [Bool.and_eq_true, Bool.or_eq_true, sqrtF_isTiny_iff d hneg, hdv, abs_of_pos hr0]
  · rintro (h | h)
    · exact absurd h (not_le.mpr hlt)
    · exact absurd h hR0

-- ANCHOR: FloatLibSqrtMeetsSpec
/-- The square root of FloatLib meets the specification of square root of Core on every bit
string of a format. -/
theorem floatlib_sqrt_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a : Nat} (ha : a < 2 ^ fmt.width) :
    SquareRootSpecOf sp fmt fmt .roundTiesToEven a (flSqrt fmt a) := by
  cases h : sqrtExceptional fmt a
  · exact floatlib_sqrt_meets_spec_of_finite sp hc ha h
  · exact floatlib_sqrt_meets_spec_of_exceptional sp hc ha h
-- ANCHOR_END: FloatLibSqrtMeetsSpec

end SoftFloat.FloatLib.Proof
