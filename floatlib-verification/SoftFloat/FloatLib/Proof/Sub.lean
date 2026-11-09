/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Add

/-!
# Subtraction of FloatLib against the specification of SoftFloat

FloatLib subtracts by adding the second operand with its sign bit toggled. This module proves
that the public subtraction of FloatLib, rounded to nearest with ties to even and with its
status, meets `SubtractionSpecOf` when an operand is a NaN or an infinity, by the same result
for addition applied to the toggled second operand.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b : Nat}

/-- The operands for which `SubtractionSpecOf` does not take its rounded branch: an operand is a
NaN or an infinity (`subExceptional_eq` gives the literal branch condition of `arithSumOf`). -/
def subExceptional (fmt : Format) (a b : Nat) : Bool :=
  isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b

theorem subExceptional_eq (fmt : Format) (a b : Nat) :
    subExceptional fmt a b =
      (isNaN fmt a || isNaN fmt b ||
        (arithIsInf fmt a && arithIsInf fmt b && arithSign fmt a != !arithSign fmt b) ||
        arithIsInf fmt a || arithIsInf fmt b) := by
  unfold subExceptional
  cases arithIsInf fmt a <;> cases arithIsInf fmt b <;> simp

/-! ## The second operand with its sign bit toggled -/

/-- The bit string of `b` with its sign bit toggled, as FloatLib negates it. -/
def sub_negBits (fmt : Format) (b : Nat) : Nat :=
  (Model.toggleSign (ofBits fmt b)).toNatBits

theorem sub_negBits_lt : sub_negBits fmt b < 2 ^ fmt.width :=
  (isEncoding_iff _ _).1 (isEncoding_toNatBits _)

theorem sub_ofBits_negBits : ofBits fmt (sub_negBits fmt b) = Model.toggleSign (ofBits fmt b) :=
  Model.ofNatBits_toNatBits _

theorem flSub_eq_flAdd (fmt : Format) (a b : Nat) : flSub fmt a b = flAdd fmt a (sub_negBits fmt b) := by
  unfold flSub flAdd
  rw [sub_ofBits_negBits]
  show ofOutcome (Model.Internal.Status.add (ofBits fmt a) (Model.neg (ofBits fmt b)) .nearest) = _
  rw [Model.neg_eq_toggleSign_of_supportsSignedZero _ rfl]
  rfl

theorem sub_sign_negBits (hb : b < 2 ^ fmt.width) :
    (fmt.unpack (sub_negBits fmt b)).sign = !(fmt.unpack b).sign := by
  rw [← signBit_ofBits sub_negBits_lt, sub_ofBits_negBits, Model.signBit_toggleSign,
    signBit_ofBits hb]

theorem sub_expField_negBits (hb : b < 2 ^ fmt.width) :
    (fmt.unpack (sub_negBits fmt b)).expField = (fmt.unpack b).expField := by
  rw [← expField_ofBits sub_negBits_lt, sub_ofBits_negBits, Model.expField_toggleSign,
    expField_ofBits hb]

theorem sub_fracField_negBits (hb : b < 2 ^ fmt.width) :
    (fmt.unpack (sub_negBits fmt b)).fracField = (fmt.unpack b).fracField := by
  rw [← fracField_ofBits sub_negBits_lt, sub_ofBits_negBits, Model.fracField_toggleSign,
    fracField_ofBits hb]

theorem sub_isNaN_negBits (hb : b < 2 ^ fmt.width) : isNaN fmt (sub_negBits fmt b) = isNaN fmt b := by
  unfold isNaN
  rw [classify_eq_fields, classify_eq_fields]
  dsimp only
  rw [sub_expField_negBits hb, sub_fracField_negBits hb]
  split_ifs <;> rfl

theorem sub_isSignalingNaN_negBits (hb : b < 2 ^ fmt.width) :
    isSignalingNaN fmt (sub_negBits fmt b) = isSignalingNaN fmt b := by
  unfold isSignalingNaN
  rw [classify_eq_fields, classify_eq_fields]
  dsimp only
  rw [sub_expField_negBits hb, sub_fracField_negBits hb]
  split_ifs <;> rfl

theorem sub_arithIsInf_negBits (hb : b < 2 ^ fmt.width) :
    arithIsInf fmt (sub_negBits fmt b) = arithIsInf fmt b := by
  unfold arithIsInf
  rw [classify_eq_fields, classify_eq_fields]
  dsimp only
  rw [sub_expField_negBits hb, sub_fracField_negBits hb]
  split_ifs <;> rfl

/-! ## The NaN that FloatLib chooses -/

/-- The NaN that FloatLib chooses for the addition of the toggled second operand is the NaN of
`floatLibNaN .subtraction`, which reverses the sign of a NaN taken from the second operand. -/
theorem sub_floatLibNaN_negBits (hb : b < 2 ^ fmt.width) :
    floatLibNaN .addition fmt [(fmt, a), (fmt, sub_negBits fmt b)] =
      floatLibNaN .subtraction fmt [(fmt, a), (fmt, b)] := by
  unfold floatLibNaN
  simp only [firstNaN, sub_isNaN_negBits hb, sub_isSignalingNaN_negBits hb]
  cases isSignalingNaN fmt a <;> cases isSignalingNaN fmt b <;>
    cases isNaN fmt a <;> cases isNaN fmt b <;>
    simp [Option.orElse, floatLibNaNSign, sub_sign_negBits hb, sub_fracField_negBits hb]

/-! ## Subtraction with an operand that is a NaN or an infinity -/

theorem floatlib_sub_meets_spec_of_not_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : subExceptional fmt a b = true) :
    SubtractionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flSub fmt a b) := by
  have hn := sub_isNaN_negBits hb
  have hsn := sub_isSignalingNaN_negBits hb
  have hi := sub_arithIsInf_negBits hb
  have hadd := floatlib_add_meets_spec_of_not_finite sp hc ha (sub_negBits_lt (b := b))
    (by rw [hn, hi]; exact hx)
  rw [← flSub_eq_flAdd] at hadd
  unfold AdditionSpecOf arithSumOf at hadd
  unfold SubtractionSpecOf arithSumOf
  rw [hc.propagateNaN .addition fmt _ (Or.inl rfl), sub_floatLibNaN_negBits hb,
    ← hc.propagateNaN .subtraction fmt _ (Or.inr (Or.inl rfl)), hn, hsn, hi] at hadd
  refine ⟨hadd.1, ?_⟩
  have h2 := hadd.2
  unfold subExceptional at hx
  cases hN : (isNaN fmt a || isNaN fmt b)
  · cases hib : arithIsInf fmt b
    · have hia : arithIsInf fmt a = true := by simp_all
      simp only [hN, hia, hib, Bool.false_eq_true, ↓reduceIte, Bool.and_false,
        Bool.false_and] at h2 ⊢
      exact h2
    · have hs : arithSign fmt (sub_negBits fmt b) = !arithSign fmt b := by
        rw [arithSign_of_arithIsInf (by rw [hi]; exact hib), arithSign_of_arithIsInf hib,
          sub_sign_negBits hb]
      simp only [hN, hib, hs, Bool.false_eq_true, ↓reduceIte, Bool.and_true] at h2 ⊢
      exact h2
  · simp only [hN, ↓reduceIte] at h2 ⊢
    exact h2

end SoftFloat.FloatLib.Proof
