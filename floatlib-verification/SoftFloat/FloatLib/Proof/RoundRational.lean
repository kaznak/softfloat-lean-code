/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Rounded
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics

/-!
# The rational rounding of FloatLib

FloatLib rounds a quotient on the path of scaled rationals, not on the dyadic one. This module
proves that a delivered value with a status meets `RoundedResultOf` for a nonzero exact value
when the value and the status pass the overflow, value, inexact and tininess tests in terms of
the boundaries `midR` and `umidR` (`ratF_meets`), and gives these tests for the scaled rationals
of FloatLib: the overflow test, the finiteness and the sign of `Model.roundRatScaled`, and the
tininess test.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format}

/-! ## A rounded result from its tests -/

/-- A delivered value and a status meet `RoundedResultOf` for a nonzero exact value `x` when the
status overflows exactly from `midR` on, the value is then an infinity and is otherwise the
rounded value, the status is inexact when the value is not `x`, and it underflows when it is
inexact and the value is subnormal or zero or `x` is below `umidR`. The value carries the sign of
`x` when it is an infinity or a zero. -/
theorem ratF_meets (sp : Specialization) (htin : sp.tininess = .afterRounding) {x : ℝ}
    (hx0 : x ≠ 0) (zn : Bool) (v : Model (toFL fmt)) (st : _root_.FloatLib.Numerics.IEEEStatus)
    (hsign : (midR fmt ≤ |x| ∨ roundR fmt .roundTiesToEven x = 0) →
      Model.signBit v = decide (x < 0))
    (hinv : st.invalid = false) (hdz : st.divideByZero = false)
    (hover : midR fmt ≤ |x| →
      Model.isInf v = true ∧ st.overflow = true ∧ st.inexact = true ∧ st.underflow = false)
    (hfin : |x| < midR fmt →
      Model.isFinite v = true ∧ Model.toReal v = roundR fmt .roundTiesToEven x ∧
        st.overflow = false ∧ (st.inexact = true ↔ Model.toReal v ≠ x) ∧
        (st.underflow = true ↔
          st.inexact = true ∧ (Model.isTinyAfterRounding v = true ∨ |x| < umidR fmt))) :
    RoundedResultOf sp fmt .roundTiesToEven x zn (v.toNatBits, flagsOf st) := by
  unfold RoundedResultOf
  refine ⟨isEncoding_toNatBits _, hinv, hdz, ?_⟩
  by_cases hO : midR fmt ≤ |x|
  · obtain ⟨hinf, ho, hi, hu⟩ := hover hO
    rw [ite_eq_left ((maxFinite_lt_abs_roundR_iff fmt _).mpr hO)]
    simp only [overflowToInfinity, ↓reduceIte]
    refine ⟨?_, ho, hi, hu⟩
    rw [classify_toNatBits_of_isInf hinf, hsign (Or.inl hO)]
  · obtain ⟨hf, hR, ho, hi, hu⟩ := hfin (lt_of_not_ge hO)
    rw [ite_eq_right (by rw [maxFinite_lt_abs_roundR_iff]; exact hO)]
    have hval : valR fmt v.toNatBits = roundR fmt .roundTiesToEven x := by
      rw [valR_toNatBits hf, hR]
    have hinex : (flagsOf st).inexact = true ↔ roundR fmt .roundTiesToEven x ≠ x := by
      rw [← hR]; exact hi
    refine ⟨isFinite_toNatBits hf, hval, ?_, ho, hinex, ?_⟩
    · -- A zero carries the sign of `x`.
      intro hR0
      have hs0 := hsign (Or.inr hR0)
      rw [← hval] at hR0
      rcases (valR_eq_zero_iff fmt _).mp hR0 with h | ⟨s, hs⟩
      · exact absurd (isFinite_toNatBits hf) h
      · have hs' := sign_of_classify_zero hs
        rw [unpack_toNatBits] at hs'
        dsimp only at hs'
        rw [hs, ← hs', hs0]
        simp only [hx0, ↓reduceIte]
    · -- Underflow: inexact and tiny.
      show st.underflow = true ↔ _
      rw [hu, show (st.inexact = true) = (roundR fmt .roundTiesToEven x ≠ x) from
        propext hinex, tiny_iff sp fmt htin]
      constructor
      · rintro ⟨hne, ht⟩
        refine ⟨hne, hx0, ?_⟩
        rcases ht with ht | ht
        · rw [Model.isTinyAfterRounding_eq_true_iff] at ht
          have hlt := abs_toReal_lt_of_expField_zero ht.1 ht.2
          rw [hR] at hlt
          by_contra hu'
          exact absurd (two_zpow_emin_le_abs_roundR fmt (not_lt.mp hu')) (not_le.mpr hlt)
        · exact ht
      · rintro ⟨hne, _, hu'⟩
        exact ⟨hne, Or.inr hu'⟩

/-! ## The tests on scaled rationals -/

theorem ratF_overflowMidpoint_significand_ne_zero (fmt : Format) :
    (Model.overflowMidpoint (toFL fmt)).significand ≠ 0 := by
  unfold Model.overflowMidpoint
  dsimp only
  omega

theorem ratF_underflowMidpoint_significand_ne_zero (fmt : Format) :
    (Model.underflowMidpoint (toFL fmt)).significand ≠ 0 := by
  have : 1 ≤ Model.pow2 (toFL fmt).fracWidth := by
    rw [Model.pow2_eq_two_pow]; exact Nat.one_le_two_pow
  unfold Model.underflowMidpoint
  dsimp only
  omega

/-- FloatLib signals overflow of a scaled rational exactly when it is at least `midR`. -/
theorem ratF_nearestEvenOverflows_iff (n d : Nat) (e : Int) (hd : d ≠ 0) :
    Model.rationalNearestEvenOverflowsScaled (toFL fmt) n d e = true ↔
      midR fmt ≤ Model.scaledRatToReal n d e := by
  unfold Model.rationalNearestEvenOverflowsScaled
  rw [Model.compareDyadicScaled?_false_eq_compare n d e _ hd rfl
    (ratF_overflowMidpoint_significand_ne_zero fmt), toReal_overflowMidpoint]
  rcases lt_trichotomy (Model.scaledRatToReal n d e) (midR fmt) with h | h | h
  · rw [compare_lt_iff_lt.mpr h]
    simp only [Bool.false_eq_true, false_iff, not_le]
    exact h
  · rw [h, compare_eq_iff_eq.mpr rfl, maxFiniteMantissaOdd_toFL]
    simp only [le_refl]
  · rw [compare_gt_iff_gt.mpr h]
    simp only [true_iff]
    exact h.le

theorem ratF_midR_le_two_zpow (fmt : Format) : midR fmt ≤ 2 ^ (emax fmt + 1) := by
  have e : (2 : ℝ) ^ (emax fmt + 1) = 2 ^ fmt.sigBits * 2 ^ (emax fmt + 1 - fmt.sigBits) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
  unfold midR
  rw [e]
  have : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
  nlinarith

theorem ratF_scaledRatToReal_bounds (n d : Nat) (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) :
    (2 : ℝ) ^ (_root_.FloatLib.Numerics.RationalBinary.floorLog2 n d + e) ≤
        Model.scaledRatToReal n d e ∧
      Model.scaledRatToReal n d e <
        (2 : ℝ) ^ (_root_.FloatLib.Numerics.RationalBinary.floorLog2 n d + e + 1) := by
  have h := Model.scaledRatToReal_floorLog2_bounds n d e hn hd
  simp only [Model.bpow, bpow_binary] at h
  exact h

theorem ratF_signedScaledRatToReal_false (n d : Nat) (e : Int) :
    Model.signedScaledRatToReal false n d e = Model.scaledRatToReal n d e := rfl

/-- Positive nearest-even rational rounding in `toFL fmt` is a finite value with a clear sign
bit, or the positive infinity of a rational at least `midR`. -/
theorem ratF_roundRatScaled_false_cases (n d : Nat) (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) :
    (Model.isFinite (Model.roundRatScaled (toFL fmt) false n d e) = true ∧
        Model.signBit (Model.roundRatScaled (toFL fmt) false n d e) = false) ∨
      (Model.roundRatScaled (toFL fmt) false n d e = Model.posInf (toFL fmt) ∧
        midR fmt ≤ Model.scaledRatToReal n d e) := by
  have hF := isIEEE_toFL fmt
  have hb := one_le_bias fmt
  have hmid := ratF_midR_le_two_zpow fmt
  have hbd := ratF_scaledRatToReal_bounds n d e hn hd
  have hmn : (toFL fmt).minNormalExponent = 1 - (fmt.bias : Int) := by
    unfold FloatFormat.minNormalExponent; rw [exponentBias_toFL]; rfl
  have hmx := maxNormalExponent_toFL fmt
  rw [Model.roundRatScaled_false_eq_of_isIEEE (toFL fmt) n d e hF hn hd]
  dsimp only
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · -- Above the normal range.
    refine Or.inr ⟨rfl, hmid.trans (le_trans ?_ hbd.1)⟩
    apply zpow_le_zpow_right₀ (by norm_num)
    unfold emax
    omega
  · exact Or.inl ⟨Model.isFinite_posZero _, Model.signBit_posZero _⟩
  · exact Or.inl ⟨Model.isFinite_posZero _, Model.signBit_posZero _⟩
  · exact Or.inl ⟨Model.isFinite_ofFields_ieee _ hF false 1 0
      (FloatFormat.one_lt_expAllOnesNat _), Model.signBit_ofFields _ _ _ _⟩
  · exact Or.inl ⟨Model.isFinite_ofFields_ieee _ hF false 0 _ (FloatFormat.expAllOnesNat_pos _),
      Model.signBit_ofFields _ _ _ _⟩
  · -- A carry out of the top binade.
    refine Or.inr ⟨rfl, ?_⟩
    have ht : _root_.FloatLib.Numerics.RationalBinary.floorLog2 n d + e =
        (toFL fmt).maxNormalExponent := by omega
    have hround := Model.roundAt_scaledRat_eq (toFL fmt) false n d e hn hd
    have htarget : Model.fexpOf (toFL fmt)
        (_root_.FloatLib.Numerics.RationalBinary.floorLog2 n d + e + 1) =
          (toFL fmt).maxNormalExponent - Int.ofNat (toFL fmt).fracWidth := by
      rw [ht]; exact Model.fexpOf_total_eq_normal _ _ (by omega)
    simp only [Bool.false_eq_true, ↓reduceIte] at hround
    rw [htarget] at hround
    have hscaled : _root_.FloatLib.Numerics.RationalBinary.scaleByPowerOfTwo n d
          (e - ((toFL fmt).maxNormalExponent - Int.ofNat (toFL fmt).fracWidth)) =
        _root_.FloatLib.Numerics.RationalBinary.scaleByPowerOfTwo n d
          (Int.ofNat (toFL fmt).fracWidth -
            _root_.FloatLib.Numerics.RationalBinary.floorLog2 n d) := by
      congr 1; omega
    rw [hscaled, h6] at hround
    have hval : roundR fmt .roundTiesToEven (Model.scaledRatToReal n d e) = 2 ^ (emax fmt + 1) := by
      rw [roundR_eq_roundAt, ← ratF_signedScaledRatToReal_false, hround, hmx, fracWidth_toFL]
      simp only [Model.bpow, bpow_binary, Model.pow2_eq_two_pow, Int.ofNat_eq_natCast]
      push_cast
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
      unfold emax
      congr 1
      push_cast
      ring
    have hq0 := Model.scaledRatToReal_nonneg n d e
    have := (maxFinite_lt_abs_roundR_iff fmt _).mp (by
      rw [hval, abs_of_pos (by positivity)]; exact maxFinite_lt_two_zpow fmt)
    rwa [abs_of_nonneg hq0] at this
  · refine Or.inl ⟨Model.isFinite_ofFields_ieee _ hF false _ 0
      (Model.Directed.Internal.encodedExponent_lt_expAllOnes_ieee _ hF _ (by omega) (by omega)),
      Model.signBit_ofFields _ _ _ _⟩
  · refine Or.inl ⟨Model.isFinite_ofFields_ieee _ hF false _ _
      (Model.Directed.Internal.encodedExponent_lt_expAllOnes_ieee _ hF _ (by omega) (by omega)),
      Model.signBit_ofFields _ _ _ _⟩

/-- Nearest-even rational rounding in `toFL fmt` with the sign `s` is a finite value, or an
infinity of a rational at least `midR`, and carries the sign `s`. -/
theorem ratF_roundRatScaled_cases (s : Bool) (n d : Nat) (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) :
    Model.signBit (Model.roundRatScaled (toFL fmt) s n d e) = s ∧
      (Model.isFinite (Model.roundRatScaled (toFL fmt) s n d e) = true ∨
        (Model.isInf (Model.roundRatScaled (toFL fmt) s n d e) = true ∧
          midR fmt ≤ Model.scaledRatToReal n d e)) := by
  have hF := isIEEE_toFL fmt
  have hinf := FloatFormat.supportsInfinity_eq_true_of_isIEEE _ hF
  have hsz := FloatFormat.supportsSignedZero_eq_true_of_isIEEE _ hF
  cases s
  · rcases ratF_roundRatScaled_false_cases (fmt := fmt) n d e hn hd with ⟨hf, hs⟩ | ⟨hv, hm⟩
    · exact ⟨hs, Or.inl hf⟩
    · rw [hv]
      exact ⟨Model.signBit_posInf _, Or.inr ⟨Model.isInf_posInf _ hinf, hm⟩⟩
  · rw [Model.roundRatScaled_true_eq_neg_false _ n d e hF hd, Model.isFinite_neg, Model.isInf_neg,
      Model.signBit_neg]
    simp only [hsz, ↓reduceIte]
    rcases ratF_roundRatScaled_false_cases (fmt := fmt) n d e hn hd with ⟨hf, hs⟩ | ⟨hv, hm⟩
    · rw [hs]
      exact ⟨rfl, Or.inl hf⟩
    · rw [hv]
      exact ⟨by rw [Model.signBit_posInf]; rfl, Or.inr ⟨Model.isInf_posInf _ hinf, hm⟩⟩

/-- The rounding of a nonzero scaled rational by FloatLib to nearest with ties to even, with the
status of FloatLib for it, meets `RoundedResultOf` for the exact value of the rational. -/
theorem ratF_roundRatScaled_meets (sp : Specialization) (htin : sp.tininess = .afterRounding)
    (s : Bool) (n d : Nat) (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) (zn : Bool) :
    RoundedResultOf sp fmt .roundTiesToEven (Model.signedScaledRatToReal s n d e) zn
      ((Model.roundRatScaled (toFL fmt) s n d e).toNatBits,
        flagsOf (Model.rationalRoundingStatusScaled (toFL fmt) .nearest s n d e
          (Model.roundRatScaled (toFL fmt) s n d e))) := by
  have hF := isIEEE_toFL fmt
  have hq := Model.scaledRatToReal_pos n d e hn hd
  have habs := Model.abs_signedScaledRatToReal s n d e
  have hx0 : Model.signedScaledRatToReal s n d e ≠ 0 := by
    intro h0; rw [h0, abs_zero] at habs; exact absurd habs hq.ne
  have hneg : decide (Model.signedScaledRatToReal s n d e < 0) = s := by
    cases s
    · rw [ratF_signedScaledRatToReal_false]; exact decide_eq_false (not_lt.mpr hq.le)
    · simp only [Model.signedScaledRatToReal, ↓reduceIte, Left.neg_neg_iff, decide_eq_true_eq]
      exact hq
  obtain ⟨hsign, hcases⟩ := ratF_roundRatScaled_cases (fmt := fmt) s n d e hn hd
  have hOiff : Model.rationalRoundingOverflowsScaled (toFL fmt) .nearest s n d e = true ↔
      midR fmt ≤ |Model.signedScaledRatToReal s n d e| := by
    rw [habs]; exact ratF_nearestEvenOverflows_iff n d e hd
  have hR : ∀ hf : Model.isFinite (Model.roundRatScaled (toFL fmt) s n d e) = true,
      Model.toReal (Model.roundRatScaled (toFL fmt) s n d e) =
        roundR fmt .roundTiesToEven (Model.signedScaledRatToReal s n d e) := fun hf => by
    rw [Model.toReal_roundRatScaled_eq_roundAt _ s n d e hF hn hd hf, roundR_eq_roundAt]
  have hstO : midR fmt ≤ |Model.signedScaledRatToReal s n d e| →
      Model.rationalRoundingStatusScaled (toFL fmt) .nearest s n d e
          (Model.roundRatScaled (toFL fmt) s n d e) = { overflow := true, inexact := true } :=
    fun h => by
      unfold Model.rationalRoundingStatusScaled
      rw [ite_eq_left (hOiff.mpr h)]
  have hstF : |Model.signedScaledRatToReal s n d e| < midR fmt →
      ∀ hf : Model.isFinite (Model.roundRatScaled (toFL fmt) s n d e) = true,
      Model.rationalRoundingStatusScaled (toFL fmt) .nearest s n d e
          (Model.roundRatScaled (toFL fmt) s n d e) =
        { underflow := Model.rationalIsTinyAfterRoundingScaled (toFL fmt) .nearest s n d e
              (Model.roundRatScaled (toFL fmt) s n d e) &&
            !(Model.rationalEqualsDyadicScaled s n d e (Model.finiteDyadic _ hf))
          inexact := !(Model.rationalEqualsDyadicScaled s n d e (Model.finiteDyadic _ hf)) } :=
    fun h hf => by
      have hO : Model.rationalRoundingOverflowsScaled (toFL fmt) .nearest s n d e = false := by
        cases h' : Model.rationalRoundingOverflowsScaled (toFL fmt) .nearest s n d e
        · rfl
        · exact absurd (hOiff.mp h') (not_le.mpr h)
      unfold Model.rationalRoundingStatusScaled
      rw [ite_eq_right (by rw [hO]; exact Bool.false_ne_true), dite_eq_left hf]
  have hfinOf : |Model.signedScaledRatToReal s n d e| < midR fmt →
      Model.isFinite (Model.roundRatScaled (toFL fmt) s n d e) = true := fun h => by
    rcases hcases with hf | ⟨_, hm⟩
    · exact hf
    · rw [habs] at h; exact absurd hm (not_le.mpr h)
  have hinfOf : midR fmt ≤ |Model.signedScaledRatToReal s n d e| →
      Model.isInf (Model.roundRatScaled (toFL fmt) s n d e) = true := fun h => by
    rcases hcases with hf | ⟨hi, _⟩
    · have hb := Model.abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite _ hF hf
      rw [toReal_posMaxFinite_toFL, hR hf] at hb
      exact absurd ((maxFinite_lt_abs_roundR_iff fmt _).mpr h) (not_lt.mpr hb)
    · exact hi
  have hinvdz : (Model.rationalRoundingStatusScaled (toFL fmt) .nearest s n d e
        (Model.roundRatScaled (toFL fmt) s n d e)).invalid = false ∧
      (Model.rationalRoundingStatusScaled (toFL fmt) .nearest s n d e
        (Model.roundRatScaled (toFL fmt) s n d e)).divideByZero = false := by
    by_cases hO : midR fmt ≤ |Model.signedScaledRatToReal s n d e|
    · rw [hstO hO]; exact ⟨rfl, rfl⟩
    · rw [hstF (lt_of_not_ge hO) (hfinOf (lt_of_not_ge hO))]; exact ⟨rfl, rfl⟩
  apply ratF_meets sp htin hx0 zn _ _ (fun _ => by rw [hsign, hneg]) hinvdz.1 hinvdz.2
  · intro h
    rw [hstO h]
    exact ⟨hinfOf h, rfl, rfl, rfl⟩
  · intro h
    have hf := hfinOf h
    rw [hstF h hf]
    have hinex : (!(Model.rationalEqualsDyadicScaled s n d e (Model.finiteDyadic _ hf))) = true ↔
        Model.toReal (Model.roundRatScaled (toFL fmt) s n d e) ≠
          Model.signedScaledRatToReal s n d e := by
      unfold Model.rationalEqualsDyadicScaled
      rw [Model.compareDyadicScaled?_eq_compare _ _ _ _ _ hd, ← Model.toReal_eq_toReal_finiteDyadic hf]
      rcases lt_trichotomy (Model.signedScaledRatToReal s n d e)
          (Model.toReal (Model.roundRatScaled (toFL fmt) s n d e)) with h1 | h1 | h1
      · rw [compare_lt_iff_lt.mpr h1]; simp only [reduceCtorEq, Option.some.injEq,
          Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, not_false_eq_true, true_iff]
        exact h1.ne'
      · rw [h1, compare_eq_iff_eq.mpr rfl]; simp
      · rw [compare_gt_iff_gt.mpr h1]; simp only [reduceCtorEq, Option.some.injEq,
          Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, not_false_eq_true, true_iff]
        exact h1.ne
    refine ⟨hf, hR hf, rfl, hinex, ?_⟩
    show (Model.rationalIsTinyAfterRoundingScaled (toFL fmt) .nearest s n d e _ && _) = true ↔
      (!(Model.rationalEqualsDyadicScaled s n d e (Model.finiteDyadic _ hf))) = true ∧ _
    rw [Bool.and_eq_true, Model.rationalIsTinyAfterRoundingScaled_eq_true_iff _ _ _ _ _ _ _ hd,
      toReal_underflowMidpoint, habs]
    cases Model.isTinyAfterRounding (Model.roundRatScaled (toFL fmt) s n d e)
    · simp only [Bool.false_eq_true, true_and, false_or]
      exact and_comm
    · simp

end SoftFloat.FloatLib.Proof
