/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Add

/-!
# Multiplication of FloatLib against the specification of SoftFloat

The public multiplication of FloatLib, rounded to nearest with ties to even and with its
status, meets `MultiplicationSpecOf` for every specialization with the choices of FloatLib. This
module proves it when an operand is a NaN or an infinity.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b : Nat}

/-- The operands for which `MultiplicationSpecOf` does not take its rounded branch: an operand
is a NaN or an infinity (`mulExceptional_eq` gives the literal branch condition). -/
def mulExceptional (fmt : Format) (a b : Nat) : Bool :=
  isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b

theorem mulExceptional_eq (fmt : Format) (a b : Nat) :
    mulExceptional fmt a b =
      (isNaN fmt a || isNaN fmt b ||
        ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) ||
        (arithIsInf fmt a || arithIsInf fmt b)) := by
  unfold mulExceptional
  cases arithIsInf fmt a <;> cases arithIsInf fmt b <;> simp

/-! ## Classification facts of SoftFloat -/

theorem mul_arithIsZero_eq (fmt : Format) (a : Nat) :
    arithIsZero fmt a = Format.isZeroU (fmt.unpack a) := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    unfold arithIsZero at h
    split at h
    · rename_i s hc
      exact ((classify_eq_zero_iff fmt a s).1 hc).1
    · cases h
  · intro h
    unfold arithIsZero
    rw [(isZeroU_unpack_iff fmt a).1 h]

theorem mul_arithSign_of_isNaN_eq_false (h : isNaN fmt a = false) :
    arithSign fmt a = (fmt.unpack a).sign := by
  unfold isNaN at h
  unfold arithSign
  rw [classify_eq_fields] at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem mul_isSignalingNaN_eq_false (h : isNaN fmt a = false) : isSignalingNaN fmt a = false := by
  cases h' : isSignalingNaN fmt a
  · rfl
  · rw [isNaN_of_isSignalingNaN h'] at h; cases h

theorem mul_arithIsInf_eq_false_of_arithIsZero (h : arithIsZero fmt a = true) :
    arithIsInf fmt a = false := by
  unfold arithIsZero at h
  unfold arithIsInf
  split <;> simp_all

theorem mul_isZero_ofBits (ha : a < 2 ^ fmt.width) :
    Model.isZero (ofBits fmt a) = arithIsZero fmt a := by
  rw [model_isZero, isZero_ofBits ha, mul_arithIsZero_eq]

/-! ## The value and the status of the multiplication of FloatLib -/

theorem flMul_fst (fmt : Format) (a b : Nat) :
    (flMul fmt a b).1 = (Model.Spec.mul (ofBits fmt a) (ofBits fmt b)).toNatBits := by
  show (Model.mul (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)).value.toNatBits = _
  rw [Model.value_mul, Model.Proof.mul_eq_spec]

/-- The invalid flag of FloatLib for a multiplication with an operand that is a NaN or an
infinity: a signaling NaN, or an infinity times a zero and no NaN. -/
def mulInvalid (fmt : Format) (a b : Nat) : Bool :=
  isSignalingNaN fmt a || isSignalingNaN fmt b ||
    (!(isNaN fmt a || isNaN fmt b) &&
      ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsInf fmt b && arithIsZero fmt a)))

theorem flMul_snd_of_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none) :
    (flMul fmt a b).2 = { invalidOperation := mulInvalid fmt a b } := by
  show flagsOf (Model.Internal.Status.mul (ofBits fmt a) (ofBits fmt b) .nearest).status = _
  unfold Model.Internal.Status.mul
  split
  · rename_i hx hy
    rcases h with h | h <;> simp_all
  · dsimp only
    rw [flagsOf_outcomeWithInvalid, model_isSNaN, model_isSNaN, model_isNaN, model_isNaN,
      isInf_ofBits' ha, isInf_ofBits' hb, mul_isZero_ofBits ha, mul_isZero_ofBits hb,
      isSNaN_ofBits ha, isSNaN_ofBits hb, isNaN_ofBits ha, isNaN_ofBits hb]
    rfl

/-! ## The NaN that FloatLib chooses -/

theorem mul_floatLibNaN_eq (fmt : Format) (xs : List (Format × Nat)) :
    floatLibNaN .multiplication fmt xs = floatLibNaN .addition fmt xs := rfl

theorem mul_classify_nativeOverflow (s : Bool) :
    classify fmt (Model.nativeOverflow (toFL fmt) s).toNatBits = .infinity s := by
  have hlt : (Model.nativeOverflow (toFL fmt) s).toNatBits < 2 ^ fmt.width :=
    (isEncoding_iff _ _).1 (isEncoding_toNatBits _)
  rw [classify_eq_infinity_iff, ← isInf_ofBits hlt, ← signBit_ofBits hlt]
  unfold ofBits
  rw [Model.ofNatBits_toNatBits, ← model_isInf]
  cases s
  · exact ⟨Model.isInf_posInf _ rfl, Model.signBit_posInf _⟩
  · exact ⟨Model.isInf_negInf _ rfl, Model.signBit_negInf _⟩

/-! ## The value of the specification of multiplication of FloatLib, case by case -/

section
variable {x y : Model (toFL fmt)}

theorem specMul_nan (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none) {n : Model (toFL fmt)}
    (hch : Model.chooseNaN2 x y = some n) : Model.Spec.mul x y = n := by
  unfold Model.Spec.mul
  split
  · rcases h with h | h <;> simp_all
  · simp [hch]

theorem specMul_left (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none)
    (hch : Model.chooseNaN2 x y = none) (hx : Model.isInf x = true) :
    Model.Spec.mul x y = if Model.isZero y then Model.invalidResult (toFL fmt)
      else Model.nativeOverflow (toFL fmt) (Model.signBit x != Model.signBit y) := by
  unfold Model.Spec.mul
  split
  · rcases h with h | h <;> simp_all
  · simp [hch, hx]

theorem specMul_right (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none)
    (hch : Model.chooseNaN2 x y = none) (hx : Model.isInf x = false) (hy : Model.isInf y = true) :
    Model.Spec.mul x y = if Model.isZero x then Model.invalidResult (toFL fmt)
      else Model.nativeOverflow (toFL fmt) (Model.signBit x != Model.signBit y) := by
  unfold Model.Spec.mul
  split
  · rcases h with h | h <;> simp_all
  · simp [hch, hx, hy]

end

/-! ## Multiplication with an operand that is a NaN or an infinity -/

theorem floatlib_mul_meets_spec_of_not_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : mulExceptional fmt a b = true) :
    MultiplicationSpecOf sp fmt fmt fmt .roundTiesToEven a b (flMul fmt a b) := by
  have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
    rw [toDyadic?_ofBits_eq_none_iff ha, toDyadic?_ofBits_eq_none_iff hb]
    unfold mulExceptional at hx
    simp only [Bool.or_eq_true] at hx ⊢
    tauto
  have hia := isInf_ofBits' ha
  have hib := isInf_ofBits' hb
  have hza := mul_isZero_ofBits ha
  have hzb := mul_isZero_ofBits hb
  unfold MultiplicationSpecOf
  dsimp only
  refine ⟨by rw [flMul_fst]; exact isEncoding_toNatBits _, ?_⟩
  rw [flMul_snd_of_none ha hb hnone, flMul_fst,
    hc.propagateNaN .multiplication fmt _ (Or.inr (Or.inr (Or.inl rfl))), mul_floatLibNaN_eq]
  unfold mulInvalid
  split_ifs with h1 h2 h3
  · -- A NaN operand: FloatLib delivers the NaN it chooses, quieted.
    obtain ⟨nan, hch, hbits⟩ := chooseNaN2_add ha hb h1
    rw [specMul_nan hnone hch]
    exact ⟨hbits, by simp [h1]⟩
  · -- An infinity times a zero: the canonical NaN, and invalid.
    have hch := chooseNaN2_none ha hb h1
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hval : Model.Spec.mul (ofBits fmt a) (ofBits fmt b) = Model.invalidResult (toFL fmt) := by
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h2
      rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · rw [specMul_left hnone hch (by rw [hia, h2a]), hzb, h2b]
        rfl
      · have hfa := mul_arithIsInf_eq_false_of_arithIsZero h2a
        rw [specMul_right hnone hch (by rw [hia, hfa]) (by rw [hib, h2b]), hza, h2a]
        rfl
    rw [hval, toNatBits_invalidResult, floatLibNaN_no_nan h1]
    refine ⟨rfl, ?_⟩
    simp only [mul_isSignalingNaN_eq_false hna, mul_isSignalingNaN_eq_false hnb, hna, hnb]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h2
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> simp [h2a, h2b]
  · -- An infinity times a number that is not zero: the infinity of the sign of the product.
    have hch := chooseNaN2_none ha hb h1
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsign : (Model.signBit (ofBits fmt a) != Model.signBit (ofBits fmt b)) =
        (arithSign fmt a != arithSign fmt b) := by
      rw [signBit_ofBits ha, signBit_ofBits hb, mul_arithSign_of_isNaN_eq_false hna,
        mul_arithSign_of_isNaN_eq_false hnb]
    simp only [Bool.or_eq_true, Bool.and_eq_true, not_or, not_and] at h2
    obtain ⟨h2l, h2r⟩ := h2
    have hval : Model.Spec.mul (ofBits fmt a) (ofBits fmt b) =
        Model.nativeOverflow (toFL fmt) (arithSign fmt a != arithSign fmt b) := by
      cases h' : arithIsInf fmt a
      · have hbi : arithIsInf fmt b = true := by simp_all
        have hza' : arithIsZero fmt a = false := by
          cases h'' : arithIsZero fmt a
          · rfl
          · exact absurd hbi (h2r h'')
        rw [specMul_right hnone hch (by rw [hia, h']) (by rw [hib, hbi]), hza, hza', ← hsign]
        rfl
      · have hzb' : arithIsZero fmt b = false := by
          cases h'' : arithIsZero fmt b
          · rfl
          · exact absurd h'' (h2l h')
        rw [specMul_left hnone hch (by rw [hia, h']), hzb, hzb', ← hsign]
        rfl
    rw [hval, mul_classify_nativeOverflow]
    refine ⟨rfl, ?_⟩
    simp only [mul_isSignalingNaN_eq_false hna, mul_isSignalingNaN_eq_false hnb, hna, hnb]
    cases h' : arithIsInf fmt a <;> cases h'' : arithIsInf fmt b <;>
      cases hz : arithIsZero fmt a <;> cases hz' : arithIsZero fmt b <;> simp_all
  · -- Otherwise both operands are finite, against the hypothesis.
    unfold mulExceptional at hx
    simp_all

end SoftFloat.FloatLib.Proof
