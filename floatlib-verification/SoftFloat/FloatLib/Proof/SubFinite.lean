/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Sub
import SoftFloat.FloatLib.Proof.AddFinite

/-!
# Subtraction of FloatLib against the specification of SoftFloat: finite operands

FloatLib subtracts by adding the second operand with its sign bit toggled. When both operands
are finite, the toggled operand is finite, its value is the negated value of the second operand
and its sign is reversed, so the result for addition gives `SubtractionSpecOf`.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b : Nat}

/-- The value of the toggled second operand is the negated value. -/
theorem subF_valR_negBits (hb : b < 2 ^ fmt.width) :
    valR fmt (sub_negBits fmt b) = -valR fmt b := by
  unfold valR
  rw [classify_eq_fields, classify_eq_fields]
  dsimp only
  rw [sub_expField_negBits hb, sub_fracField_negBits hb, sub_sign_negBits hb]
  cases (fmt.unpack b).sign <;> split_ifs <;> simp_all

/-- The sign of the toggled second operand, when it is not a NaN, is reversed. -/
theorem subF_arithSign_negBits (hb : b < 2 ^ fmt.width) (hn : isNaN fmt b = false) :
    arithSign fmt (sub_negBits fmt b) = !arithSign fmt b := by
  rw [arithSign_eq fmt (by rw [sub_isNaN_negBits hb]; exact hn), arithSign_eq fmt hn,
    sub_sign_negBits hb]

/-- The subtraction of FloatLib meets the specification of SoftFloat when both operands are
finite. -/
theorem floatlib_sub_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : subExceptional fmt a b = false) :
    SubtractionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flSub fmt a b) := by
  have hn := sub_isNaN_negBits hb
  have hi := sub_arithIsInf_negBits hb
  have hadd := floatlib_add_meets_spec_of_finite sp hc ha (sub_negBits_lt (b := b))
    (by rw [hn, hi]; exact hx)
  rw [← flSub_eq_flAdd] at hadd
  unfold subExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨hna, hnb⟩, hia⟩, hib⟩ := hx
  unfold AdditionSpecOf arithSumOf at hadd
  unfold SubtractionSpecOf arithSumOf
  refine ⟨hadd.1, ?_⟩
  have h2 := hadd.2
  simp only [hn, hi, hna, hnb, hia, hib, Bool.or_false, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte] at h2 ⊢
  rw [subF_valR_negBits hb, subF_arithSign_negBits hb hnb, ← sub_eq_add_neg] at h2
  rw [← sub_eq_add_neg]
  exact h2

-- ANCHOR: FloatLibSubMeetsSpec
/-- The subtraction of FloatLib meets the specification of subtraction of Core on every pair of
bit strings of a format. -/
theorem floatlib_sub_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) :
    SubtractionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flSub fmt a b) := by
  cases h : subExceptional fmt a b
  · exact floatlib_sub_meets_spec_of_finite sp hc ha hb h
  · exact floatlib_sub_meets_spec_of_not_finite sp hc ha hb h
-- ANCHOR_END: FloatLibSubMeetsSpec

end SoftFloat.FloatLib.Proof
