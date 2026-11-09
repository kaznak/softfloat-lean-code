/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Spec.Choices
import SoftFloat.FloatLib.Proof.Add
import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof

/-!
# Division of FloatLib against the specification of SoftFloat

The public division of FloatLib, rounded to nearest with ties to even and with its status,
meets `DivisionSpecOf` for every specialization with the choices of FloatLib. This module
proves it when the specification does not take its rounded branch: an operand is a NaN or an
infinity, or the divisor is a zero.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b : Nat}

/-! ## Classification facts of SoftFloat and of FloatLib -/

theorem div_isSignalingNaN_eq_false (h : isNaN fmt a = false) : isSignalingNaN fmt a = false := by
  cases h' : isSignalingNaN fmt a
  · rfl
  · rw [isNaN_of_isSignalingNaN h'] at h; cases h

theorem div_arithIsZero_eq (fmt : Format) (a : Nat) :
    arithIsZero fmt a = Format.isZeroU (fmt.unpack a) := by
  cases hz : Format.isZeroU (fmt.unpack a)
  · unfold arithIsZero
    split
    · rename_i s hc
      have := ((classify_eq_zero_iff fmt a s).1 hc).1
      rw [hz] at this
      cases this
    · rfl
  · unfold arithIsZero
    rw [(isZeroU_unpack_iff fmt a).1 hz]

theorem div_arithSign_eq (h : isNaN fmt a = false) : arithSign fmt a = (fmt.unpack a).sign := by
  unfold isNaN at h
  unfold arithSign
  rw [classify_eq_fields] at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all

theorem div_isNaN_eq_false_of_arithIsZero (h : arithIsZero fmt a = true) : isNaN fmt a = false := by
  unfold arithIsZero at h
  unfold isNaN
  split at h <;> simp_all

theorem div_arithIsInf_eq_false_of_arithIsZero (h : arithIsZero fmt a = true) :
    arithIsInf fmt a = false := by
  unfold arithIsZero at h
  unfold arithIsInf
  split at h <;> simp_all

theorem div_isZero_ofBits (ha : a < 2 ^ fmt.width) :
    Model.isZero (ofBits fmt a) = arithIsZero fmt a := by
  rw [model_isZero, isZero_ofBits ha, div_arithIsZero_eq]

theorem div_isNaN_ofBits (ha : a < 2 ^ fmt.width) :
    Model.isNaN (ofBits fmt a) = isNaN fmt a := by
  rw [model_isNaN, isNaN_ofBits ha]

theorem div_isSNaN_ofBits (ha : a < 2 ^ fmt.width) :
    Model.isSNaN (ofBits fmt a) = isSignalingNaN fmt a := by
  rw [model_isSNaN, isSNaN_ofBits ha]

theorem div_toDyadic?_some (ha : a < 2 ^ fmt.width) (hn : isNaN fmt a = false)
    (hi : arithIsInf fmt a = false) : ∃ d, Model.toDyadic? (ofBits fmt a) = some d := by
  cases h : Model.toDyadic? (ofBits fmt a) with
  | none =>
      rw [toDyadic?_ofBits_eq_none_iff ha, hn, hi] at h
      cases h
  | some d => exact ⟨d, rfl⟩

theorem div_isIEEE_toFL (fmt : Format) : (toFL fmt).isIEEE = true := by
  unfold toFL
  exact FloatFormat.isIEEE_ieee _ _ _ _

/-! ## The class of a value of FloatLib as a bit string of SoftFloat -/

theorem div_classify_of_isInf (x : Model (toFL fmt)) (h : Model.isInf x = true) :
    classify fmt x.toNatBits = .infinity (Model.signBit x) := by
  have hn : x.toNatBits < 2 ^ fmt.width := isEncoding_toNatBits x
  have hx : ofBits fmt x.toNatBits = x := Model.ofNatBits_toNatBits x
  rw [model_isInf, ← hx, isInf_ofBits hn] at h
  rw [classify_eq_infinity_iff]
  refine ⟨h, ?_⟩
  rw [← signBit_ofBits hn, hx]

theorem div_classify_of_isZero (x : Model (toFL fmt)) (h : Model.isZero x = true) :
    classify fmt x.toNatBits = .zero (Model.signBit x) := by
  have hn : x.toNatBits < 2 ^ fmt.width := isEncoding_toNatBits x
  have hx : ofBits fmt x.toNatBits = x := Model.ofNatBits_toNatBits x
  rw [model_isZero, ← hx, isZero_ofBits hn] at h
  rw [classify_eq_zero_iff]
  refine ⟨h, ?_⟩
  rw [← signBit_ofBits hn, hx]

theorem div_classify_nativeOverflow (s : Bool) :
    classify fmt (Model.nativeOverflow (toFL fmt) s).toNatBits = .infinity s := by
  have hinf : Model.isInf (Model.nativeOverflow (toFL fmt) s) = true := by
    rw [Model.nativeOverflow_eq_signedInf_of_isIEEE _ (div_isIEEE_toFL fmt)]
    cases s
    · exact Model.isInf_posInf _ rfl
    · exact Model.isInf_negInf _ rfl
  have hs : Model.signBit (Model.nativeOverflow (toFL fmt) s) = s := by
    rw [Model.nativeOverflow_eq_signedInf_of_isIEEE _ (div_isIEEE_toFL fmt)]
    cases s
    · exact Model.signBit_posInf _
    · exact Model.signBit_negInf _
  rw [div_classify_of_isInf _ hinf, hs]

theorem div_classify_zero (s : Bool) :
    classify fmt (Model.zero (toFL fmt) s).toNatBits = .zero s := by
  have hz : Model.isZero (Model.zero (toFL fmt) s) = true := by
    rw [Model.zero_eq_signedZero_of_isIEEE _ (div_isIEEE_toFL fmt)]
    cases s
    · exact Model.isZero_posZero _
    · exact Model.isZero_negZero _ rfl
  have hs : Model.signBit (Model.zero (toFL fmt) s) = s := by
    rw [Model.signBit_zero]
    cases s <;> rfl
  rw [div_classify_of_isZero _ hz, hs]

theorem div_xor_eq_bne (p q : Bool) : Bool.xor p q = (p != q) := by
  cases p <;> cases q <;> rfl

/-! ## The NaN that FloatLib chooses, for any arithmetic operation -/

theorem div_chooseNaN2 (op : NaNOperation) (hop : op ≠ .subtraction)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : (isNaN fmt a || isNaN fmt b) = true) :
    ∃ nan, Model.chooseNaN2 (ofBits fmt a) (ofBits fmt b) = some nan ∧
      nan.toNatBits = floatLibNaN op fmt [(fmt, a), (fmt, b)] := by
  have hi : ∀ i, ¬ (op = .subtraction ∧ i = 1) := fun _ hc => hop hc.1
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
      | exact (floatLibNaN_of_nan ha hna op 0 (hi 0)).symm
      | exact (floatLibNaN_of_nan hb hnb op 1 (hi 1)).symm
      | simp at ia ib h

theorem div_floatLibNaN_no_nan (op : NaNOperation) (h : ¬ (isNaN fmt a || isNaN fmt b) = true) :
    floatLibNaN op fmt [(fmt, a), (fmt, b)] = fmt.pack false fmt.expMax fmt.quietBit := by
  have hna : isNaN fmt a = false := by simp_all
  have hnb : isNaN fmt b = false := by simp_all
  have hsa := div_isSignalingNaN_eq_false hna
  have hsb := div_isSignalingNaN_eq_false hnb
  unfold floatLibNaN
  simp [firstNaN, hna, hnb, hsa, hsb, Option.orElse]
  rfl

/-! ## The outcome of the division of FloatLib, case by case -/

theorem flDiv_fst (fmt : Format) (a b : Nat) :
    (flDiv fmt a b).1 = (Model.Spec.div (ofBits fmt a) (ofBits fmt b)).toNatBits := by
  show (Model.div (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true)).value.toNatBits = _
  rw [Model.value_div, Model.Proof.div_eq_spec]

/-- The invalid flag of FloatLib for a division with an operand that is a NaN or an infinity. -/
def divInvalid (fmt : Format) (a b : Nat) : Bool :=
  isSignalingNaN fmt a || isSignalingNaN fmt b ||
    (!(isNaN fmt a || isNaN fmt b) && (arithIsInf fmt a && arithIsInf fmt b))

theorem flDiv_snd_of_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (h : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none) :
    (flDiv fmt a b).2 = { invalidOperation := divInvalid fmt a b } := by
  show flagsOf (Model.Internal.Status.div (ofBits fmt a) (ofBits fmt b) .nearest).status = _
  unfold Model.Internal.Status.div
  split
  · rename_i hx hy
    rcases h with h | h <;> simp_all
  · dsimp only
    rw [flagsOf_outcomeWithInvalid, div_isSNaN_ofBits ha, div_isSNaN_ofBits hb, div_isNaN_ofBits ha,
      div_isNaN_ofBits hb, isInf_ofBits' ha, isInf_ofBits' hb]
    rfl

theorem specDiv_of_none {x y : Model (toFL fmt)}
    (h : Model.toDyadic? x = none ∨ Model.toDyadic? y = none) :
    Model.Spec.div x y = Model.Spec.divSpecial x y := by
  unfold Model.Spec.div
  split
  · rcases h with h | h <;> simp_all
  · rfl

theorem flDiv_zero_div_zero {dx dy : _root_.FloatLib.Numerics.Dyadic}
    (hx : Model.toDyadic? (ofBits fmt a) = some dx) (hy : Model.toDyadic? (ofBits fmt b) = some dy)
    (hdx : dx.significand = 0) (hdy : dy.significand = 0) :
    flDiv fmt a b = ((Model.invalidResult (toFL fmt)).toNatBits, { invalidOperation := true }) := by
  show ofOutcome (Model.Internal.Status.div (ofBits fmt a) (ofBits fmt b) .nearest) = _
  unfold Model.Internal.Status.div
  rw [hx, hy]
  simp only [hdx, hdy, beq_self_eq_true, ↓reduceIte]
  rfl

theorem flDiv_nonzero_div_zero {dx dy : _root_.FloatLib.Numerics.Dyadic}
    (hx : Model.toDyadic? (ofBits fmt a) = some dx) (hy : Model.toDyadic? (ofBits fmt b) = some dy)
    (hdx : dx.significand ≠ 0) (hdy : dy.significand = 0) :
    flDiv fmt a b = ((Model.nativeOverflow (toFL fmt) (Bool.xor dx.negative dy.negative)).toNatBits,
      { divideByZero := true }) := by
  show ofOutcome (Model.Internal.Status.div (ofBits fmt a) (ofBits fmt b) .nearest) = _
  unfold Model.Internal.Status.div
  rw [hx, hy]
  have hdx' : (dx.significand == 0) = false := by simpa using hdx
  simp only [hdx', hdy, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
  rfl

/-! ## Division when the specification does not round -/

/-- The condition under which `DivisionSpecOf` does not take its rounded branch: an operand is a
NaN or an infinity, or the divisor is a zero. Its complement is that both operands are finite
(neither a NaN nor an infinity) and the divisor is not a zero. -/
def divExceptional (fmt : Format) (a b : Nat) : Bool :=
  isNaN fmt a || isNaN fmt b || arithIsInf fmt a || arithIsInf fmt b || arithIsZero fmt b

/-- Outside `divExceptional`, `DivisionSpecOf` is its rounded branch. -/
theorem divisionSpecOf_of_not_exceptional (sp : Specialization) (fmt dst : Format)
    (rm : RoundingDirection) (a b : Nat) (r : Nat × StatusFlags)
    (hx : divExceptional fmt a b = false) :
    DivisionSpecOf sp fmt fmt dst rm a b r ↔
      dst.IsEncoding r.1 ∧
        RoundedResultOf sp dst rm (valR fmt a / valR fmt b) (arithSign fmt a != arithSign fmt b) r := by
  unfold divExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨⟨hna, hnb⟩, hia⟩, hib⟩, hzb⟩ := hx
  unfold DivisionSpecOf
  simp [hna, hnb, hia, hib, hzb]

theorem floatlib_div_meets_spec_of_exceptional (sp : Specialization) (hc : FloatLibChoices sp)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hx : divExceptional fmt a b = true) :
    DivisionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flDiv fmt a b) := by
  have hia := isInf_ofBits' ha
  have hib := isInf_ofBits' hb
  have hza := div_isZero_ofBits ha
  have hzb := div_isZero_ofBits hb
  have hsa := signBit_ofBits ha
  have hsb := signBit_ofBits hb
  unfold DivisionSpecOf
  refine ⟨by rw [flDiv_fst]; exact isEncoding_toNatBits _, ?_⟩
  rw [hc.propagateNaN .division fmt _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
  split_ifs with h1 h2 h3 h4 h5
  · -- A NaN operand: FloatLib delivers the NaN it chooses, quieted.
    have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
      rw [toDyadic?_ofBits_eq_none_iff ha, toDyadic?_ofBits_eq_none_iff hb]
      simp only [Bool.or_eq_true] at h1 ⊢
      tauto
    obtain ⟨nan, hch, hbits⟩ := div_chooseNaN2 .division (by decide) ha hb h1
    rw [flDiv_snd_of_none ha hb hnone, flDiv_fst, specDiv_of_none hnone]
    unfold Model.Spec.divSpecial
    rw [hch]
    refine ⟨hbits, ?_⟩
    unfold divInvalid
    simp [h1]
  · have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsa' := div_isSignalingNaN_eq_false hna
    have hsb' := div_isSignalingNaN_eq_false hnb
    rw [div_floatLibNaN_no_nan .division h1]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h2
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
    · -- Two infinities: the canonical NaN, and invalid.
      have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
        rw [toDyadic?_ofBits_eq_none_iff ha]
        simp [h2a]
      rw [flDiv_snd_of_none ha hb hnone, flDiv_fst, specDiv_of_none hnone]
      unfold Model.Spec.divSpecial
      rw [chooseNaN2_none ha hb h1]
      simp only [hia, hib, h2a, h2b, ↓reduceIte]
      rw [toNatBits_invalidResult]
      refine ⟨rfl, ?_⟩
      unfold divInvalid
      simp [hna, hnb, hsa', hsb', h2a, h2b]
    · -- Two zeros: the canonical NaN, and invalid.
      obtain ⟨dx, hdx⟩ := div_toDyadic?_some ha hna (div_arithIsInf_eq_false_of_arithIsZero h2a)
      obtain ⟨dy, hdy⟩ := div_toDyadic?_some hb hnb (div_arithIsInf_eq_false_of_arithIsZero h2b)
      have hzx : dx.significand = 0 := by
        have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdx
        rw [hza, h2a] at this
        simpa using this.symm
      have hzy : dy.significand = 0 := by
        have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdy
        rw [hzb, h2b] at this
        simpa using this.symm
      rw [flDiv_zero_div_zero hdx hdy hzx hzy, toNatBits_invalidResult]
      exact ⟨rfl, rfl⟩
  · -- The dividend is an infinity and the divisor is finite: an infinity.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsa' := div_isSignalingNaN_eq_false hna
    have hsb' := div_isSignalingNaN_eq_false hnb
    have hfb : arithIsInf fmt b = false := by simp_all
    have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
      rw [toDyadic?_ofBits_eq_none_iff ha]
      simp [h3]
    rw [flDiv_snd_of_none ha hb hnone, flDiv_fst, specDiv_of_none hnone]
    unfold Model.Spec.divSpecial
    rw [chooseNaN2_none ha hb h1]
    simp only [hia, hib, h3, hfb, ↓reduceIte, Bool.false_eq_true]
    rw [div_classify_nativeOverflow, hsa, hsb, div_arithSign_eq hna, div_arithSign_eq hnb]
    refine ⟨rfl, ?_⟩
    unfold divInvalid
    simp [hna, hnb, hsa', hsb', hfb]
  · -- The divisor is an infinity and the dividend is finite: a zero.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hsa' := div_isSignalingNaN_eq_false hna
    have hsb' := div_isSignalingNaN_eq_false hnb
    have hfa : arithIsInf fmt a = false := by simp_all
    have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none := by
      rw [toDyadic?_ofBits_eq_none_iff hb]
      simp [h4]
    rw [flDiv_snd_of_none ha hb hnone, flDiv_fst, specDiv_of_none hnone]
    unfold Model.Spec.divSpecial
    rw [chooseNaN2_none ha hb h1]
    simp only [hia, hib, h4, hfa, ↓reduceIte, Bool.false_eq_true]
    rw [div_classify_zero, hsa, hsb, div_arithSign_eq hna, div_arithSign_eq hnb]
    refine ⟨rfl, ?_⟩
    unfold divInvalid
    simp [hna, hnb, hsa', hsb', hfa]
  · -- A finite nonzero dividend over a zero: an infinity, and division by zero.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hfa : arithIsInf fmt a = false := by simp_all
    have hfb : arithIsInf fmt b = false := by simp_all
    have hza' : arithIsZero fmt a = false := by simp_all
    obtain ⟨dx, hdx⟩ := div_toDyadic?_some ha hna hfa
    obtain ⟨dy, hdy⟩ := div_toDyadic?_some hb hnb hfb
    have hzx : dx.significand ≠ 0 := by
      have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdx
      rw [hza, hza'] at this
      intro h0
      rw [h0] at this
      cases this
    have hzy : dy.significand = 0 := by
      have := Model.isZero_eq_beq_zero_of_toDyadic?_some hdy
      rw [hzb, h5] at this
      simpa using this.symm
    rw [flDiv_nonzero_div_zero hdx hdy hzx hzy, div_classify_nativeOverflow,
      Model.sign_eq_signBit_of_toDyadic?_some hdx, Model.sign_eq_signBit_of_toDyadic?_some hdy,
      div_xor_eq_bne, hsa, hsb, div_arithSign_eq hna, div_arithSign_eq hnb]
    exact ⟨rfl, rfl⟩
  · -- Otherwise the specification rounds, against the hypothesis.
    unfold divExceptional at hx
    simp_all

end SoftFloat.FloatLib.Proof
