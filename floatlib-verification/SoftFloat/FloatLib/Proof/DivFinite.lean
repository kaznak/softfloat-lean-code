/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Div
import SoftFloat.FloatLib.Proof.RoundRational

/-!
# Division of FloatLib against the specification of SoftFloat: finite operands

With both operands finite and the divisor nonzero, the public division of FloatLib delivers an
exact signed zero for a zero dividend, and otherwise rounds the exact quotient, a scaled
rational, once to nearest with ties to even and reports the status of that rounding. It meets
`DivisionSpecOf` for every specialization with the choices of FloatLib.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

variable {fmt : Format} {a b : Nat}

/-- The division of FloatLib with a zero dividend and a nonzero divisor, both finite. -/
theorem flDiv_zero_div_nonzero {dx dy : Dyadic}
    (hx : Model.toDyadic? (ofBits fmt a) = some dx) (hy : Model.toDyadic? (ofBits fmt b) = some dy)
    (hdx : dx.significand = 0) (hdy : dy.significand ≠ 0) :
    flDiv fmt a b = ((Model.zero (toFL fmt) (Bool.xor dx.negative dy.negative)).toNatBits,
      flagsOf .clear) := by
  show ofOutcome (Model.Internal.Status.div (ofBits fmt a) (ofBits fmt b) .nearest) = _
  unfold Model.Internal.Status.div
  rw [hx, hy]
  have hdy' : (dy.significand == 0) = false := by simpa using hdy
  simp only [hdy', hdx, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- The division of FloatLib with two finite nonzero operands: the rounded exact quotient and the
status of the rounding. -/
theorem flDiv_nonzero_div_nonzero {dx dy : Dyadic}
    (hx : Model.toDyadic? (ofBits fmt a) = some dx) (hy : Model.toDyadic? (ofBits fmt b) = some dy)
    (hdx : dx.significand ≠ 0) (hdy : dy.significand ≠ 0) :
    flDiv fmt a b =
      ((Model.roundRatScaled (toFL fmt) (Bool.xor dx.negative dy.negative) dx.significand
          dy.significand (dx.exponent - dy.exponent)).toNatBits,
        flagsOf (Model.rationalRoundingStatusScaled (toFL fmt) .nearest
          (Bool.xor dx.negative dy.negative) dx.significand dy.significand
          (dx.exponent - dy.exponent)
          (Model.roundRatScaled (toFL fmt) (Bool.xor dx.negative dy.negative) dx.significand
            dy.significand (dx.exponent - dy.exponent)))) := by
  show ofOutcome (Model.div (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)) = _
  rw [Model.div_status_of_toDyadic_nonzero .nearest hx hy hdx hdy]
  rfl

/-- The division of FloatLib meets the specification of SoftFloat when both operands are finite
and the divisor is not a zero. -/
theorem floatlib_div_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : divExceptional fmt a b = false) :
    DivisionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flDiv fmt a b) := by
  rw [divisionSpecOf_of_not_exceptional sp fmt fmt _ a b _ hx]
  unfold divExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨⟨hna, hnb⟩, hia⟩, hib⟩, hzb⟩ := hx
  have hfa : IsFinite fmt a :=
    isFinite_of_not_isNaN_not_isInfU fmt hna (by rw [← arithIsInf_eq]; exact hia)
  have hfb : IsFinite fmt b :=
    isFinite_of_not_isNaN_not_isInfU fmt hnb (by rw [← arithIsInf_eq]; exact hib)
  have hdx := toDyadic?_ofBits ha hfa
  have hdy := toDyadic?_ofBits hb hfb
  set dx := decodeU fmt (fmt.unpack a)
  set dy := decodeU fmt (fmt.unpack b)
  have hzy : dy.significand ≠ 0 := by
    have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdy
    rw [div_isZero_ofBits hb, hzb] at this
    intro h0
    rw [h0] at this
    cases this
  have hsign : Bool.xor dx.negative dy.negative = (arithSign fmt a != arithSign fmt b) := by
    rw [div_xor_eq_bne, decodeU_negative, decodeU_negative, arithSign_eq fmt hna,
      arithSign_eq fmt hnb]
  have hq : valR fmt a / valR fmt b = Model.signedScaledRatToReal (Bool.xor dx.negative dy.negative)
      dx.significand dy.significand (dx.exponent - dy.exponent) := by
    rw [Model.signedScaledRatToReal_eq_div_toReal, toReal_decodeU hfa, toReal_decodeU hfb]
  by_cases hzx : dx.significand = 0
  · -- A zero dividend: an exact zero with the sign of the quotient.
    rw [flDiv_zero_div_nonzero hdx hdy hzx hzy]
    have h0 : valR fmt a = 0 := by
      rw [← toReal_decodeU hfa, (toReal_eq_zero_iff dx).mpr hzx]
    have hfin : Model.isFinite (Model.zero (toFL fmt) (Bool.xor dx.negative dy.negative)) = true := by
      rw [Model.zero_eq_signedZero_of_isIEEE _ (isIEEE_toFL fmt)]
      exact isFinite_signedZero_toFL _
    refine ⟨isEncoding_toNatBits _, ?_⟩
    rw [h0, zero_div]
    unfold RoundedResultOf
    rw [roundR_zero, abs_zero]
    simp only [not_lt.mpr (maxFinite_pos fmt).le, ↓reduceIte]
    refine ⟨isEncoding_toNatBits _, rfl, rfl, isFinite_toNatBits hfin, ?_, ?_, rfl, ?_, ?_⟩
    · rw [valR_toNatBits hfin, Model.toReal_zero]
    · intro _
      rw [div_classify_zero, hsign]
    · simp [flagsOf, _root_.FloatLib.Numerics.IEEEStatus.clear]
    · simp [flagsOf, _root_.FloatLib.Numerics.IEEEStatus.clear]
  · -- A nonzero dividend: the quotient rounded once.
    rw [flDiv_nonzero_div_nonzero hdx hdy hzx hzy]
    refine ⟨isEncoding_toNatBits _, ?_⟩
    rw [hq, ← hsign]
    exact ratF_roundRatScaled_meets sp hc.tininess _ _ _ _ hzx hzy _

-- ANCHOR: FloatLibDivMeetsSpec
/-- The division of FloatLib meets the specification of division of Core on every pair of bit
strings of a format. -/
theorem floatlib_div_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) :
    DivisionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flDiv fmt a b) := by
  cases h : divExceptional fmt a b
  · exact floatlib_div_meets_spec_of_finite sp hc ha hb h
  · exact floatlib_div_meets_spec_of_exceptional sp hc ha hb h
-- ANCHOR_END: FloatLibDivMeetsSpec

end SoftFloat.FloatLib.Proof
