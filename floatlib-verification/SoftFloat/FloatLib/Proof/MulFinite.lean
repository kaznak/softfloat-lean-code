/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Mul
import SoftFloat.FloatLib.Proof.Rounded

/-!
# Multiplication of FloatLib against the specification of SoftFloat: finite operands

With both operands finite, FloatLib returns the zero of the sign of the product when a
significand is zero, and otherwise rounds the exact dyadic product once. The zero is the rounding
of the exact product too, so in both cases the result is the rounded exact product with the status
of that rounding, and it meets `MultiplicationSpecOf`.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

variable {fmt : Format} {a b : Nat}

/-- The exact dyadic product that FloatLib rounds. -/
def mulF_exact (dx dy : Dyadic) : Dyadic :=
  { negative := Bool.xor dx.negative dy.negative
    significand := dx.significand * dy.significand
    exponent := dx.exponent + dy.exponent }

/-- The rounding of a dyadic with significand zero is the zero of its sign.

The proof follows that of the private lemma `roundDyadic_mant_zero` of FloatLib
(`FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/Finite.lean`, at the commit fixed in the
lakefile; Copyright (c) 2026 FloatLib, released under the MIT License). -/
theorem mulF_roundDyadic_significand_zero (f : FloatFormat) (sign : Bool) (exp : Int) :
    Model.roundDyadic f { negative := sign, significand := 0, exponent := exp } =
      Model.zero f sign := by
  by_cases hfmt : f.isIEEE = true
  · have hencoding : f.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff f).mp hfmt).1
    cases sign <;>
      simp [Model.roundDyadic, hfmt, Model.ieeeRoundDyadic, Model.zero,
        FloatFormat.supportsSignedZero, hencoding,
        Model.posZero_eq_ofModel_zero, Model.negZero_eq_ofModel_zero]
  · simp [Model.roundDyadic, hfmt, Model.roundDyadicGeneral]

/-- On finite operands the specification of multiplication of FloatLib is the rounded exact
product, also when a significand is zero. -/
theorem mulF_specMul_of_toDyadic {f : FloatFormat} {x y : Model f} {dx dy : Dyadic}
    (hx : Model.toDyadic? x = some dx) (hy : Model.toDyadic? y = some dy) :
    Model.Spec.mul x y = Model.roundDyadic f (mulF_exact dx dy) := by
  unfold Model.Spec.mul
  rw [hx, hy]
  dsimp only
  by_cases h : (dx.significand == 0 || dy.significand == 0) = true
  · rw [ite_eq_left h]
    have h0 : dx.significand * dy.significand = 0 := by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h <;> simp [h]
    unfold mulF_exact
    rw [h0, mulF_roundDyadic_significand_zero]
  · rw [ite_eq_right h]
    rfl

/-- The multiplication of FloatLib on two finite operands: the rounded exact product and the
status of the rounding. -/
theorem mulF_flMul_of_toDyadic {dx dy : Dyadic} (hx : Model.toDyadic? (ofBits fmt a) = some dx)
    (hy : Model.toDyadic? (ofBits fmt b) = some dy) :
    flMul fmt a b =
      ((Model.roundDyadic (toFL fmt) (mulF_exact dx dy)).toNatBits,
        flagsOf (Model.dyadicRoundingStatus (toFL fmt) .nearest (mulF_exact dx dy)
          (Model.roundDyadic (toFL fmt) (mulF_exact dx dy)))) := by
  have hv : Model.mul (ofBits fmt a) (ofBits fmt b) =
      Model.roundDyadic (toFL fmt) (mulF_exact dx dy) := by
    rw [Model.Proof.mul_eq_spec, mulF_specMul_of_toDyadic hx hy]
  show ofOutcome (Model.mul (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)) = _
  rw [Model.mul_status_of_toDyadic .nearest hx hy]
  dsimp only
  unfold ofOutcome
  rw [hv]
  rfl

/-- The multiplication of FloatLib meets the specification of SoftFloat when both operands are
finite. -/
theorem floatlib_mul_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : mulExceptional fmt a b = false) :
    MultiplicationSpecOf sp fmt fmt fmt .roundTiesToEven a b (flMul fmt a b) := by
  unfold mulExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨hna, hnb⟩, hia⟩, hib⟩ := hx
  have hfa : IsFinite fmt a :=
    isFinite_of_not_isNaN_not_isInfU fmt hna (by rw [← arithIsInf_eq]; exact hia)
  have hfb : IsFinite fmt b :=
    isFinite_of_not_isNaN_not_isInfU fmt hnb (by rw [← arithIsInf_eq]; exact hib)
  have hprod : (mulF_exact (decodeU fmt (fmt.unpack a)) (decodeU fmt (fmt.unpack b))).toReal =
      valR fmt a * valR fmt b := by
    unfold mulF_exact
    rw [Model.Dyadic.toReal_mul, toReal_decodeU hfa, toReal_decodeU hfb]
  have hzero :
      (mulF_exact (decodeU fmt (fmt.unpack a)) (decodeU fmt (fmt.unpack b))).significand = 0 →
      (mulF_exact (decodeU fmt (fmt.unpack a)) (decodeU fmt (fmt.unpack b))).negative =
        (arithSign fmt a != arithSign fmt b) := by
    intro _
    unfold mulF_exact
    dsimp only
    rw [arithSign_eq fmt hna, arithSign_eq fmt hnb, decodeU_negative, decodeU_negative]
  have hmeets := roundDyadic_meets (fmt := fmt) sp hc.tininess _ _ hzero
  rw [hprod] at hmeets
  unfold MultiplicationSpecOf
  dsimp only
  rw [mulF_flMul_of_toDyadic (toDyadic?_ofBits ha hfa) (toDyadic?_ofBits hb hfb)]
  refine ⟨isEncoding_toNatBits _, ?_⟩
  simp only [hna, hnb, hia, hib, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]
  exact hmeets

-- ANCHOR: FloatLibMulMeetsSpec
/-- The multiplication of FloatLib meets the specification of multiplication of Core on every pair
of bit strings of a format. -/
theorem floatlib_mul_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) :
    MultiplicationSpecOf sp fmt fmt fmt .roundTiesToEven a b (flMul fmt a b) := by
  cases h : mulExceptional fmt a b
  · exact floatlib_mul_meets_spec_of_finite sp hc ha hb h
  · exact floatlib_mul_meets_spec_of_not_finite sp hc ha hb h
-- ANCHOR_END: FloatLibMulMeetsSpec

end SoftFloat.FloatLib.Proof
