/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Add
import SoftFloat.FloatLib.Proof.Rounded

/-!
# Addition of FloatLib against the specification of SoftFloat: finite operands

With both operands finite, the public addition of FloatLib rounds the exact dyadic sum once, to
nearest with ties to even, and reports the status of that rounding. It meets `AdditionSpecOf` for
every specialization with the choices of FloatLib.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

/-- An exact sum that is zero is negative only when both operands are. -/
theorem addDyadic_negative_of_significand_eq_zero (x y : Dyadic)
    (h : (Model.addDyadic x y).significand = 0) :
    (Model.addDyadic x y).negative = (x.negative && y.negative) := by
  unfold Model.addDyadic _root_.FloatLib.Numerics.Dyadic.add
    _root_.FloatLib.Numerics.Dyadic.addFields at *
  dsimp only at *
  split_ifs at * <;> simp_all

theorem arithZeroSumNegative_roundTiesToEven (sa sb : Bool) :
    arithZeroSumNegative .roundTiesToEven sa sb = (sa && sb) := by
  unfold arithZeroSumNegative
  cases sa <;> cases sb <;> simp

variable {fmt : Format} {a b : Nat}

/-- The addition of FloatLib on two finite operands: the rounded exact sum and the status of the
rounding. -/
theorem flAdd_of_toDyadic {dx dy : Dyadic} (hx : Model.toDyadic? (ofBits fmt a) = some dx)
    (hy : Model.toDyadic? (ofBits fmt b) = some dy) :
    flAdd fmt a b =
      ((Model.roundDyadic (toFL fmt) (Model.addDyadic dx dy)).toNatBits,
        flagsOf (Model.dyadicRoundingStatus (toFL fmt) .nearest (Model.addDyadic dx dy)
          (Model.roundDyadic (toFL fmt) (Model.addDyadic dx dy)))) := by
  have hv : Model.Spec.add (ofBits fmt a) (ofBits fmt b) =
      Model.roundDyadic (toFL fmt) (Model.addDyadic dx dy) := by
    unfold Model.Spec.add
    rw [hx, hy]
  have hst := Model.add_status_of_toDyadic (x := ofBits fmt a) (y := ofBits fmt b) .nearest hx hy
  rw [Model.Proof.add_eq_spec, hv] at hst
  show ofOutcome (Model.add (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)) = _
  rw [hst]
  rfl

/-- The addition of FloatLib meets the specification of SoftFloat when both operands are finite. -/
theorem floatlib_add_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hfin : (isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b) = false) :
    AdditionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flAdd fmt a b) := by
  simp only [Bool.or_eq_false_iff] at hfin
  obtain ⟨⟨⟨hna, hnb⟩, hia⟩, hib⟩ := hfin
  have hfa : IsFinite fmt a :=
    isFinite_of_not_isNaN_not_isInfU fmt hna (by rw [← arithIsInf_eq]; exact hia)
  have hfb : IsFinite fmt b :=
    isFinite_of_not_isNaN_not_isInfU fmt hnb (by rw [← arithIsInf_eq]; exact hib)
  set dx := decodeU fmt (fmt.unpack a)
  set dy := decodeU fmt (fmt.unpack b)
  have hsum : (Model.addDyadic dx dy).toReal = valR fmt a + valR fmt b := by
    rw [Model.Dyadic.toReal_addDyadic, toReal_decodeU hfa, toReal_decodeU hfb]
  have hzero : (Model.addDyadic dx dy).significand = 0 →
      (Model.addDyadic dx dy).negative =
        arithZeroSumNegative .roundTiesToEven (arithSign fmt a) (arithSign fmt b) := by
    intro h0
    rw [addDyadic_negative_of_significand_eq_zero dx dy h0, arithZeroSumNegative_roundTiesToEven,
      arithSign_eq fmt hna, arithSign_eq fmt hnb, decodeU_negative, decodeU_negative]
  have hmeets := roundDyadic_meets (fmt := fmt) sp hc.tininess (Model.addDyadic dx dy) _ hzero
  rw [hsum] at hmeets
  unfold AdditionSpecOf arithSumOf
  rw [flAdd_of_toDyadic (toDyadic?_ofBits ha hfa) (toDyadic?_ofBits hb hfb)]
  refine ⟨isEncoding_toNatBits _, ?_⟩
  simp only [hna, hnb, hia, hib, Bool.or_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact hmeets

-- ANCHOR: FloatLibAddMeetsSpec
/-- The addition of FloatLib meets the specification of addition of Core on every pair of bit
strings of a format. -/
theorem floatlib_add_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) :
    AdditionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flAdd fmt a b) := by
  cases h : (isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b)
  · exact floatlib_add_meets_spec_of_finite sp hc ha hb h
  · exact floatlib_add_meets_spec_of_not_finite sp hc ha hb h
-- ANCHOR_END: FloatLibAddMeetsSpec

end SoftFloat.FloatLib.Proof
