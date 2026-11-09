/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.RoundDyadic

/-!
# The rounding of FloatLib meets `RoundedResultOf`

The value of `Model.roundDyadic`, the rounding of an exact dyadic to nearest with ties to even,
as a bit string, with the flags of `Model.dyadicRoundingStatus`, is a rounded result of the exact
value in the sense of SoftFloat, for every specialization that detects tininess after rounding.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

variable {fmt : Format}

theorem toReal_posMaxFinite_toFL (fmt : Format) :
    Model.toReal (Model.posMaxFinite (toFL fmt)) = maxFinite fmt := by
  have h1 : 1 ≤ 2 ^ fmt.fracBits := Nat.one_le_two_pow
  have hs := sigBits_eq_fracBits_add_one fmt
  rw [Model.toReal_posMaxFinite, maxFinite_eq, Model.bpow, bpow_binary, maxFiniteFracField_toFL,
    maxNormalExponent_toFL, fracWidth_toFL, Model.pow2_eq_two_pow]
  unfold emax
  have : 2 ^ fmt.fracBits + (2 ^ fmt.fracBits - 1) = 2 ^ fmt.sigBits - 1 := by
    rw [hs, pow_succ]; omega
  rw [this]
  simp only [Int.ofNat_eq_natCast]

theorem abs_toReal_lt_of_expField_zero {v : Model (toFL fmt)} (hfin : Model.isFinite v = true)
    (he : Model.expField v = 0) : |Model.toReal v| < 2 ^ emin fmt := by
  rw [← valR_toNatBits hfin, valR_eq_sigOf fmt (isFinite_toNatBits hfin), unpack_toNatBits]
  simp only [Format.sigOf, Format.ulpExpOf, he, ↓reduceIte]
  have hf : Model.fracField v < 2 ^ fmt.fracBits := by
    rw [fracField_eq, fracWidth_toFL]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have e : (2 : ℝ) ^ emin fmt = 2 ^ fmt.fracBits * 2 ^ ((1 : Int) - fmt.bias - fmt.fracBits) := by
    rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; unfold emin emax; ring_nf
  rw [e, mul_assoc, abs_sign_mul _ _ (by positivity)]
  apply mul_lt_mul_of_pos_right _ (by positivity)
  exact_mod_cast hf

theorem toReal_roundDyadic (d : Dyadic) (hfin : Model.isFinite (Model.roundDyadic (toFL fmt) d) = true) :
    Model.toReal (Model.roundDyadic (toFL fmt) d) = roundR fmt .roundTiesToEven d.toReal := by
  rw [Model.toReal_roundDyadic_eq_roundAt _ (isIEEE_toFL fmt) d hfin, roundR_eq_roundAt]

/-- The status of FloatLib when the rounding overflows. -/
theorem dyadicRoundingStatus_of_overflows {d : Dyadic} {v : Model (toFL fmt)}
    (h : Model.dyadicNearestEvenOverflows (toFL fmt) d = true) :
    Model.dyadicRoundingStatus (toFL fmt) .nearest d v = { overflow := true, inexact := true } := by
  unfold Model.dyadicRoundingStatus Model.dyadicRoundingOverflows
  rw [ite_eq_left h]

/-- The status of FloatLib when the rounding does not overflow and the rounded value is finite. -/
theorem dyadicRoundingStatus_of_isFinite {d : Dyadic} {v : Model (toFL fmt)}
    (h : Model.dyadicNearestEvenOverflows (toFL fmt) d = false) (hv : Model.isFinite v = true) :
    Model.dyadicRoundingStatus (toFL fmt) .nearest d v =
      { underflow := Model.dyadicIsTinyAfterRounding (toFL fmt) .nearest d v &&
          (Model.cmpDyadic d (Model.finiteDyadic v hv) != .eq)
        inexact := Model.cmpDyadic d (Model.finiteDyadic v hv) != .eq } := by
  unfold Model.dyadicRoundingStatus Model.dyadicRoundingOverflows
  simp only [h, Bool.false_eq_true, ↓reduceIte, hv, ↓reduceDIte]

theorem sign_of_classify_zero {n : Nat} {s : Bool} (h : classify fmt n = .zero s) :
    (fmt.unpack n).sign = s :=
  ((classify_eq_zero_iff fmt n s).mp h).2

/-- The rounding of FloatLib to nearest with ties to even, with its status, meets
`RoundedResultOf` for the exact value of the dyadic. The sign of an exact zero is the sign of the
dyadic, which is `zn`. -/
theorem roundDyadic_meets (sp : Specialization) (htin : sp.tininess = .afterRounding) (d : Dyadic)
    (zn : Bool) (hz : d.significand = 0 → d.negative = zn) :
    RoundedResultOf sp fmt .roundTiesToEven d.toReal zn
      ((Model.roundDyadic (toFL fmt) d).toNatBits,
        flagsOf (Model.dyadicRoundingStatus (toFL fmt) .nearest d (Model.roundDyadic (toFL fmt) d))) := by
  have hsign := signBit_roundDyadic (fmt := fmt) d
  unfold RoundedResultOf
  dsimp only
  by_cases hO : midR fmt ≤ |d.toReal|
  · -- The rounding overflows: FloatLib delivers the infinity of the sign of the exact value.
    have hO' := (nearestEvenOverflows_iff d).mpr hO
    rw [dyadicRoundingStatus_of_overflows hO']
    have h0 : d.significand ≠ 0 := by
      intro h0
      rw [(toReal_eq_zero_iff d).mpr h0, abs_zero] at hO
      exact absurd hO (not_le.mpr (midR_pos fmt))
    have hneg : decide (d.toReal < 0) = d.negative := by
      have := toReal_neg_iff d h0
      cases hn : d.negative <;> simp_all
    have hnf : Model.isFinite (Model.roundDyadic (toFL fmt) d) = false := by
      by_contra hf
      rw [Bool.not_eq_false] at hf
      have hb := Model.abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite _ (isIEEE_toFL fmt) hf
      rw [toReal_posMaxFinite_toFL, toReal_roundDyadic d hf] at hb
      exact absurd ((maxFinite_lt_abs_roundR_iff fmt _).mpr hO) (not_lt.mpr hb)
    have hinf : Model.isInf (Model.roundDyadic (toFL fmt) d) = true := by
      rcases isFinite_or_isInf_roundDyadic (fmt := fmt) d with h | h
      · rw [hnf] at h; cases h
      · exact h
    refine ⟨isEncoding_toNatBits _, rfl, rfl, ?_⟩
    rw [ite_eq_left ((maxFinite_lt_abs_roundR_iff fmt _).mpr hO)]
    simp only [overflowToInfinity, ↓reduceIte]
    refine ⟨?_, rfl, rfl, rfl⟩
    rw [classify_toNatBits_of_isInf hinf, hsign, hneg]
  · -- The rounding does not overflow: the rounded value is finite.
    have hO' : Model.dyadicNearestEvenOverflows (toFL fmt) d = false := by
      cases h : Model.dyadicNearestEvenOverflows (toFL fmt) d
      · rfl
      · exact absurd ((nearestEvenOverflows_iff d).mp h) hO
    have hfin := isFinite_roundDyadic_of_lt d (lt_of_not_ge hO)
    rw [dyadicRoundingStatus_of_isFinite hO' hfin]
    have hR := toReal_roundDyadic d hfin
    have hval : valR fmt (Model.roundDyadic (toFL fmt) d).toNatBits =
        roundR fmt .roundTiesToEven d.toReal := by
      rw [valR_toNatBits hfin, hR]
    have hinex : (Model.cmpDyadic d (Model.finiteDyadic _ hfin) != .eq) = true ↔
        roundR fmt .roundTiesToEven d.toReal ≠ d.toReal := by
      rw [bne_iff_ne, ne_eq, Model.cmpDyadic_eq_iff, ← Model.toReal_eq_toReal_finiteDyadic hfin, hR]
      exact ⟨fun h1 h2 => h1 h2.symm, fun h1 h2 => h1 h2.symm⟩
    refine ⟨isEncoding_toNatBits _, rfl, rfl, ?_⟩
    rw [ite_eq_right (by rw [maxFinite_lt_abs_roundR_iff]; exact hO)]
    refine ⟨isFinite_toNatBits hfin, hval, ?_, rfl, hinex, ?_⟩
    · -- A zero carries the sign of the dyadic.
      intro hR0
      rw [← hval] at hR0
      rcases (valR_eq_zero_iff fmt _).mp hR0 with h | ⟨s, hs⟩
      · exact absurd (isFinite_toNatBits hfin) h
      · have hs' := sign_of_classify_zero hs
        rw [unpack_toNatBits] at hs'
        dsimp only at hs'
        rw [hsign] at hs'
        rw [hs, ← hs']
        split_ifs with hx
        · rw [hz ((toReal_eq_zero_iff d).mp hx)]
        · have := toReal_neg_iff d (fun h => hx ((toReal_eq_zero_iff d).mpr h))
          cases hn : d.negative <;> simp_all
    · -- Underflow: inexact and tiny.
      show (Model.dyadicIsTinyAfterRounding (toFL fmt) .nearest d _ &&
          (Model.cmpDyadic d (Model.finiteDyadic _ hfin) != .eq)) = true ↔ _
      rw [Bool.and_eq_true, hinex, tiny_iff sp fmt htin, Model.dyadicIsTinyAfterRounding_eq_true_iff]
      simp only [lt_underflowMidpoint_iff]
      constructor
      · rintro ⟨ht, hne⟩
        have hx0 : d.toReal ≠ 0 := by
          intro h0; rw [h0, roundR_zero] at hne; exact hne rfl
        refine ⟨hne, hx0, ?_⟩
        rcases ht with ht | ⟨_, ht⟩
        · rw [Model.isTinyAfterRounding_eq_true_iff] at ht
          have hlt := abs_toReal_lt_of_expField_zero ht.1 ht.2
          rw [hR] at hlt
          by_contra hu
          exact absurd (two_zpow_emin_le_abs_roundR fmt (not_lt.mp hu)) (not_le.mpr hlt)
        · exact ht
      · rintro ⟨hne, _, hu⟩
        refine ⟨?_, hne⟩
        cases h : Model.isTinyAfterRounding (Model.roundDyadic (toFL fmt) d)
        · exact Or.inr ⟨rfl, hu⟩
        · exact Or.inl rfl

end SoftFloat.FloatLib.Proof
