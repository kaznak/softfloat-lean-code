/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Spec.Choices
import SoftFloat.FloatLib.Proof.Values
import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof

/-!
# Addition of FloatLib against the specification of SoftFloat

The public addition of FloatLib, rounded to nearest with ties to even and with its status,
meets `AdditionSpecOf` for every specialization with the choices of FloatLib. This module
proves it when an operand is a NaN or an infinity.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b : Nat}

/-! ## Classification facts of SoftFloat -/

theorem isNaN_of_isSignalingNaN (h : isSignalingNaN fmt a = true) : isNaN fmt a = true := by
  unfold isSignalingNaN at h
  unfold isNaN
  simp only [beq_iff_eq] at h
  rw [h]

theorem classify_of_arithIsInf (h : arithIsInf fmt a = true) :
    classify fmt a = .infinity (arithSign fmt a) := by
  unfold arithIsInf at h
  unfold arithSign
  split at h <;> simp_all

theorem isNaN_eq_false_of_arithIsInf (h : arithIsInf fmt a = true) : isNaN fmt a = false := by
  unfold isNaN
  rw [classify_of_arithIsInf h]

/-! ## The value and the status of the addition of FloatLib -/

theorem flAdd_fst (fmt : Format) (a b : Nat) :
    (flAdd fmt a b).1 = (Model.Spec.add (ofBits fmt a) (ofBits fmt b)).toNatBits := by
  show (Model.add (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)).value.toNatBits = _
  rw [Model.value_add, Model.Proof.add_eq_spec]

theorem flagsOf_outcomeWithInvalid (v : Model (toFL fmt)) (inv : Bool) :
    flagsOf (Model.outcomeWithInvalid v inv).status = { invalidOperation := inv } := by
  cases inv <;> rfl

/-- The invalid flag of FloatLib for an addition with an operand that is a NaN or an infinity:
a signaling NaN, or infinities of opposite signs and no NaN. -/
def addInvalid (fmt : Format) (a b : Nat) : Bool :=
  isSignalingNaN fmt a || isSignalingNaN fmt b ||
    (!(isNaN fmt a || isNaN fmt b) &&
      (arithIsInf fmt a && arithIsInf fmt b && (fmt.unpack a).sign != (fmt.unpack b).sign))

theorem flAdd_snd_of_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none) :
    (flAdd fmt a b).2 = { invalidOperation := addInvalid fmt a b } := by
  show flagsOf (Model.Internal.Status.add (ofBits fmt a) (ofBits fmt b) .nearest).status = _
  unfold Model.Internal.Status.add
  split
  · rename_i hx hy
    rcases h with h | h <;> simp_all
  · dsimp only
    rw [flagsOf_outcomeWithInvalid, model_isSNaN, model_isSNaN, model_isNaN, model_isNaN,
      model_isInf, model_isInf, isSNaN_ofBits ha, isSNaN_ofBits hb, isNaN_ofBits ha, isNaN_ofBits hb,
      isInf_ofBits ha, isInf_ofBits hb, signBit_ofBits ha, signBit_ofBits hb, ← arithIsInf_eq,
      ← arithIsInf_eq]
    rfl

/-! ## The NaN that FloatLib chooses -/

theorem floatLibNaN_of_nan (ha : a < 2 ^ fmt.width) (hn : isNaN fmt a = true) (op : NaNOperation)
    (i : Nat) (hi : ¬ (op = .subtraction ∧ i = 1)) :
    fmt.pack (floatLibNaNSign op i (fmt.unpack a).sign) fmt.expMax
        (2 ^ (fmt.fracBits - 1) +
          if (fmt.unpack a).fracField % 2 ^ (fmt.fracBits - 1) < 2 ^ (fmt.fracBits - 1)
          then (fmt.unpack a).fracField % 2 ^ (fmt.fracBits - 1) else 0) =
      (Model.quietNaN (ofBits fmt a)).toNatBits := by
  rw [toNatBits_quietNaN ha hn]
  simp only [Nat.mod_lt _ (Nat.two_pow_pos _), ↓reduceIte]
  have hs : floatLibNaNSign op i (fmt.unpack a).sign = (fmt.unpack a).sign := by
    unfold floatLibNaNSign
    split <;> simp_all
  rw [hs]
  rfl

theorem chooseNaN2_add (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : (isNaN fmt a || isNaN fmt b) = true) :
    ∃ nan, Model.chooseNaN2 (ofBits fmt a) (ofBits fmt b) = some nan ∧
      nan.toNatBits = floatLibNaN .addition fmt [(fmt, a), (fmt, b)] := by
  unfold Model.chooseNaN2 floatLibNaN
  simp only [firstNaN, model_isSNaN, model_isNaN, isSNaN_ofBits ha, isSNaN_ofBits hb,
    isNaN_ofBits ha, isNaN_ofBits hb]
  have ia : isSignalingNaN fmt a = true → isNaN fmt a = true := isNaN_of_isSignalingNaN
  have ib : isSignalingNaN fmt b = true → isNaN fmt b = true := isNaN_of_isSignalingNaN
  cases hsa : isSignalingNaN fmt a <;> cases hsb : isSignalingNaN fmt b <;>
    cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b <;>
    simp only [hsa, hsb, hna, hnb, Bool.false_eq_true, ↓reduceIte, Option.orElse, Option.some.injEq,
      exists_eq_left'] at ia ib h ⊢ <;>
    first
      | exact (floatLibNaN_of_nan ha hna .addition 0 (by simp)).symm
      | exact (floatLibNaN_of_nan hb hnb .addition 1 (by simp)).symm
      | simp at ia ib h

theorem chooseNaN2_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : ¬ (isNaN fmt a || isNaN fmt b) = true) :
    Model.chooseNaN2 (ofBits fmt a) (ofBits fmt b) = none := by
  have hna : isNaN fmt a = false := by simp_all
  have hnb : isNaN fmt b = false := by simp_all
  have hsa : isSignalingNaN fmt a = false := by
    cases h' : isSignalingNaN fmt a
    · rfl
    · rw [isNaN_of_isSignalingNaN h'] at hna; cases hna
  have hsb : isSignalingNaN fmt b = false := by
    cases h' : isSignalingNaN fmt b
    · rfl
    · rw [isNaN_of_isSignalingNaN h'] at hnb; cases hnb
  unfold Model.chooseNaN2
  simp [model_isSNaN, model_isNaN, isSNaN_ofBits ha, isSNaN_ofBits hb, isNaN_ofBits ha,
    isNaN_ofBits hb, hna, hnb, hsa, hsb]

theorem floatLibNaN_no_nan (h : ¬ (isNaN fmt a || isNaN fmt b) = true) :
    floatLibNaN .addition fmt [(fmt, a), (fmt, b)] = fmt.pack false fmt.expMax fmt.quietBit := by
  have hna : isNaN fmt a = false := by simp_all
  have hnb : isNaN fmt b = false := by simp_all
  have hsa : isSignalingNaN fmt a = false := by
    cases h' : isSignalingNaN fmt a
    · rfl
    · rw [isNaN_of_isSignalingNaN h'] at hna; cases hna
  have hsb : isSignalingNaN fmt b = false := by
    cases h' : isSignalingNaN fmt b
    · rfl
    · rw [isNaN_of_isSignalingNaN h'] at hnb; cases hnb
  unfold floatLibNaN
  simp [firstNaN, hna, hnb, hsa, hsb, Option.orElse]
  rfl

/-! ## The value of the specification of addition of FloatLib, case by case -/

section
variable {x y : Model (toFL fmt)}

theorem specAdd_nan (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none) {n : Model (toFL fmt)}
    (hch : Model.chooseNaN2 x y = some n) : Model.Spec.add x y = n := by
  unfold Model.Spec.add
  split
  · rcases h with h | h <;> simp_all
  · simp [hch]

theorem specAdd_invalid (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none)
    (hch : Model.chooseNaN2 x y = none) (hx : Model.isInf x = true) (hy : Model.isInf y = true)
    (hs : Model.signBit x ≠ Model.signBit y) : Model.Spec.add x y = Model.invalidResult (toFL fmt) := by
  unfold Model.Spec.add
  split
  · rcases h with h | h <;> simp_all
  · simp [hch, hx, hy, hs]

theorem specAdd_left (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none)
    (hch : Model.chooseNaN2 x y = none) (hx : Model.isInf x = true)
    (hy : Model.isInf y = true → Model.signBit x = Model.signBit y) : Model.Spec.add x y = x := by
  unfold Model.Spec.add
  split
  · rcases h with h | h <;> simp_all
  · cases hiy : Model.isInf y <;> simp_all

theorem specAdd_right (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none)
    (hch : Model.chooseNaN2 x y = none) (hx : Model.isInf x = false) (hy : Model.isInf y = true) :
    Model.Spec.add x y = y := by
  unfold Model.Spec.add
  split
  · rcases h with h | h <;> simp_all
  · simp [hch, hx, hy]

end

theorem isInf_ofBits' (ha : a < 2 ^ fmt.width) : Model.isInf (ofBits fmt a) = arithIsInf fmt a := by
  rw [model_isInf, isInf_ofBits ha, arithIsInf_eq]

/-! ## Addition with an operand that is a NaN or an infinity -/

theorem floatlib_add_meets_spec_of_not_finite (sp : Specialization) (hc : FloatLibChoices sp)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : (isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b) = true) :
    AdditionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flAdd fmt a b) := by
  have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
    rw [toDyadic?_ofBits_eq_none_iff ha, toDyadic?_ofBits_eq_none_iff hb]
    simp only [Bool.or_eq_true] at hx ⊢
    tauto
  have hia := isInf_ofBits' ha
  have hib := isInf_ofBits' hb
  have hsa := signBit_ofBits ha
  have hsb := signBit_ofBits hb
  unfold AdditionSpecOf arithSumOf
  refine ⟨by rw [flAdd_fst]; exact isEncoding_toNatBits _, ?_⟩
  rw [flAdd_snd_of_none ha hb hnone, flAdd_fst, hc.propagateNaN .addition fmt _ (Or.inl rfl)]
  unfold addInvalid
  split_ifs with h1 h2 h3 h4
  · -- A NaN operand: FloatLib delivers the NaN it chooses, quieted.
    obtain ⟨nan, hch, hbits⟩ := chooseNaN2_add ha hb h1
    rw [specAdd_nan hnone hch]
    exact ⟨hbits, by simp [h1]⟩
  · -- Infinities of opposite signs: the canonical NaN, and invalid.
    have hch := chooseNaN2_none ha hb h1
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
    obtain ⟨⟨h2a, h2b⟩, h2s⟩ := h2
    rw [arithSign_of_arithIsInf h2a, arithSign_of_arithIsInf h2b] at h2s
    rw [specAdd_invalid hnone hch (by rw [hia, h2a]) (by rw [hib, h2b]) (by rw [hsa, hsb]; exact h2s),
      toNatBits_invalidResult, floatLibNaN_no_nan h1]
    refine ⟨rfl, ?_⟩
    simp_all
  · -- The first operand is an infinity: it is delivered.
    have hch := chooseNaN2_none ha hb h1
    have hy : Model.isInf (ofBits fmt b) = true →
        Model.signBit (ofBits fmt a) = Model.signBit (ofBits fmt b) := by
      intro hyb
      rw [hib] at hyb
      rw [hsa, hsb, ← arithSign_of_arithIsInf h3, ← arithSign_of_arithIsInf hyb]
      simp_all
    rw [specAdd_left hnone hch (by rw [hia, h3]) hy, toNatBits_ofBits ha, classify_of_arithIsInf h3]
    refine ⟨rfl, ?_⟩
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsa' : isSignalingNaN fmt a = false := by
      cases h' : isSignalingNaN fmt a
      · rfl
      · rw [isNaN_of_isSignalingNaN h'] at hna; cases hna
    have hsb' : isSignalingNaN fmt b = false := by
      cases h' : isSignalingNaN fmt b
      · rfl
      · rw [isNaN_of_isSignalingNaN h'] at hnb; cases hnb
    have hinv : (arithIsInf fmt a && arithIsInf fmt b && (fmt.unpack a).sign != (fmt.unpack b).sign) = false := by
      cases hb' : arithIsInf fmt b
      · simp
      · have := hy (by rw [hib, hb'])
        rw [hsa, hsb] at this
        simp [this]
    simp [hna, hnb, hsa', hsb', hinv]
  · -- The second operand is an infinity and the first is not: the second is delivered.
    have hch := chooseNaN2_none ha hb h1
    have hfa : arithIsInf fmt a = false := by simpa using h3
    rw [specAdd_right hnone hch (by rw [hia, hfa]) (by rw [hib, h4]), toNatBits_ofBits hb,
      classify_of_arithIsInf h4]
    refine ⟨rfl, ?_⟩
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsa' : isSignalingNaN fmt a = false := by
      cases h' : isSignalingNaN fmt a
      · rfl
      · rw [isNaN_of_isSignalingNaN h'] at hna; cases hna
    have hsb' : isSignalingNaN fmt b = false := by
      cases h' : isSignalingNaN fmt b
      · rfl
      · rw [isNaN_of_isSignalingNaN h'] at hnb; cases hnb
    simp [hna, hnb, hsa', hsb', hfa]
  · -- Otherwise both operands are finite, against the hypothesis.
    simp_all

end SoftFloat.FloatLib.Proof
