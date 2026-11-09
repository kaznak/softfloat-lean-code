/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Div

/-!
# Square root of FloatLib against the specification of SoftFloat

The public square root of FloatLib, rounded to nearest with ties to even and with its status,
meets `SquareRootSpecOf` for every specialization with the choices of FloatLib. This module
proves it when the specification does not take its rounded branch: the operand is a NaN, a
zero, negative, or an infinity.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a : Nat}

/-! ## The NaN that FloatLib chooses for one operand -/

theorem sqrt_chooseNaN1 (op : NaNOperation) (ha : a < 2 ^ fmt.width) (h : isNaN fmt a = true) :
    Model.chooseNaN1 (ofBits fmt a) = some (Model.quietNaN (ofBits fmt a)) ∧
      (Model.quietNaN (ofBits fmt a)).toNatBits = floatLibNaN op fmt [(fmt, a)] := by
  refine ⟨?_, ?_⟩
  · unfold Model.chooseNaN1
    rw [div_isNaN_ofBits ha, h]
    rfl
  · have hn := (floatLibNaN_of_nan ha h op 0 (fun hc => absurd hc.2 (by decide))).symm
    unfold floatLibNaN
    cases hs : isSignalingNaN fmt a <;>
      simp only [firstNaN, hs, h, Bool.false_eq_true, ↓reduceIte, Option.orElse] <;>
      exact hn

theorem sqrt_floatLibNaN_no_nan (op : NaNOperation) (h : isNaN fmt a = false) :
    floatLibNaN op fmt [(fmt, a)] = fmt.pack false fmt.expMax fmt.quietBit := by
  have hs := div_isSignalingNaN_eq_false h
  unfold floatLibNaN
  simp [firstNaN, h, hs, Option.orElse]
  rfl

/-! ## The outcome of the square root of FloatLib -/

theorem flSqrt_fst (fmt : Format) (a : Nat) :
    (flSqrt fmt a).1 = (Model.Spec.sqrt (ofBits fmt a)).toNatBits := by
  show (Model.sqrt (ofBits fmt a) (mode := .nearest) (status := true)).value.toNatBits = _
  rw [Model.value_sqrt, Model.Proof.sqrt_eq_spec]

theorem flSqrt_snd_of_outcome {inv : Bool}
    (h : Model.sqrt (ofBits fmt a) (mode := .nearest) (status := true) =
      Model.outcomeWithInvalid (Model.sqrt (ofBits fmt a) (mode := .nearest)) inv) :
    (flSqrt fmt a).2 = { invalidOperation := inv } := by
  show flagsOf (Model.sqrt (ofBits fmt a) (mode := .nearest) (status := true)).status = _
  rw [h, flagsOf_outcomeWithInvalid]

theorem sqrt_classify_of_arithIsZero (ha : a < 2 ^ fmt.width) (h : arithIsZero fmt a = true) :
    classify fmt a = .zero (arithSign fmt a) := by
  have hz : Model.isZero (ofBits fmt a) = true := by rw [div_isZero_ofBits ha, h]
  have := div_classify_of_isZero _ hz
  rw [toNatBits_ofBits ha, signBit_ofBits ha] at this
  rw [this, div_arithSign_eq (div_isNaN_eq_false_of_arithIsZero h)]

/-! ## Square root when the specification does not round -/

/-- The condition under which `SquareRootSpecOf` does not take its rounded branch: the operand
is a NaN, a zero, negative, or an infinity. Its complement is that the operand is a positive
finite nonzero value (a positive normal or subnormal number). -/
def sqrtExceptional (fmt : Format) (a : Nat) : Bool :=
  isNaN fmt a || arithIsZero fmt a || arithSign fmt a || arithIsInf fmt a

/-- Outside `sqrtExceptional`, `SquareRootSpecOf` is its rounded branch. -/
theorem squareRootSpecOf_of_not_exceptional (sp : Specialization) (fmt dst : Format)
    (rm : RoundingDirection) (a : Nat) (r : Nat × StatusFlags)
    (hx : sqrtExceptional fmt a = false) :
    SquareRootSpecOf sp fmt dst rm a r ↔
      dst.IsEncoding r.1 ∧ RoundedResultOf sp dst rm (Real.sqrt (valR fmt a)) false r := by
  unfold sqrtExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨hn, hz⟩, hs⟩, hi⟩ := hx
  unfold SquareRootSpecOf
  simp [hn, hz, hs, hi]

theorem floatlib_sqrt_meets_spec_of_exceptional (sp : Specialization) (hc : FloatLibChoices sp)
    (ha : a < 2 ^ fmt.width) (hx : sqrtExceptional fmt a = true) :
    SquareRootSpecOf sp fmt fmt .roundTiesToEven a (flSqrt fmt a) := by
  have hia := isInf_ofBits' ha
  have hza := div_isZero_ofBits ha
  have hna := div_isNaN_ofBits ha
  have hsna := div_isSNaN_ofBits ha
  have hsa := signBit_ofBits ha
  unfold SquareRootSpecOf
  refine ⟨by rw [flSqrt_fst]; exact isEncoding_toNatBits _, ?_⟩
  rw [hc.propagateNaN .squareRoot fmt _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
  split_ifs with h1 h2 h3 h4
  · -- A NaN: FloatLib delivers it, quieted.
    obtain ⟨hch, hbits⟩ := sqrt_chooseNaN1 .squareRoot ha h1
    rw [flSqrt_fst, flSqrt_snd_of_outcome (Model.sqrt_status_of_isNaN .nearest (by rw [hna, h1])),
      hsna]
    unfold Model.Spec.sqrt
    rw [hch]
    exact ⟨hbits, rfl⟩
  · -- A zero: delivered as it is.
    have hn : isNaN fmt a = false := by simpa using h1
    rw [flSqrt_fst, flSqrt_snd_of_outcome (Model.sqrt_status_of_isZero .nearest (by rw [hza, h2]))]
    unfold Model.Spec.sqrt Model.chooseNaN1
    simp only [hna, hn, hia, div_arithIsInf_eq_false_of_arithIsZero h2, hza, h2, Bool.false_eq_true,
      ↓reduceIte]
    rw [toNatBits_ofBits ha]
    exact ⟨sqrt_classify_of_arithIsZero ha h2, trivial⟩
  · -- A negative nonzero value, an infinity included: the canonical NaN, and invalid.
    have hn : isNaN fmt a = false := by simpa using h1
    have hz : arithIsZero fmt a = false := by simpa using h2
    have hs : (fmt.unpack a).sign = true := by rw [← div_arithSign_eq hn]; exact h3
    rw [flSqrt_fst, flSqrt_snd_of_outcome (Model.sqrt_status_of_signBit .nearest (by rw [hna, hn])
      (by rw [hza, hz]) (by rw [hsa, hs])), sqrt_floatLibNaN_no_nan .squareRoot hn]
    unfold Model.Spec.sqrt Model.chooseNaN1
    simp only [hna, hn, hza, hz, hsa, hs, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, trivial⟩
    split <;> exact toNatBits_invalidResult fmt
  · -- The positive infinity: delivered as it is.
    have hn : isNaN fmt a = false := by simpa using h1
    have hs : (fmt.unpack a).sign = false := by
      rw [← div_arithSign_eq hn]; simpa using h3
    rw [flSqrt_fst, flSqrt_snd_of_outcome (Model.sqrt_status_of_isInf .nearest (by rw [hia, h4])
      (by rw [hsa, hs]))]
    unfold Model.Spec.sqrt Model.chooseNaN1
    simp only [hna, hn, hia, h4, hsa, hs, Bool.false_eq_true, ↓reduceIte]
    exact ⟨div_classify_nativeOverflow false, trivial⟩
  · -- Otherwise the specification rounds, against the hypothesis.
    unfold sqrtExceptional at hx
    simp_all

end SoftFloat.FloatLib.Proof
