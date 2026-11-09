/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Div

/-!
# Fused multiply-add of FloatLib against the specification of SoftFloat

The public fused multiply-add of FloatLib, rounded to nearest with ties to even and with its
status, meets `FusedMultiplyAddSpecOf` for every specialization with the choices of FloatLib.
This module proves it when the specification does not take its rounded branch: an operand is a
NaN or an infinity.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a b c : Nat}

/-! ## Classification facts of SoftFloat -/

theorem fma_arithIsZero_eq_false_of_arithIsInf (h : arithIsInf fmt a = true) :
    arithIsZero fmt a = false := by
  cases hz : arithIsZero fmt a
  · rfl
  · rw [div_arithIsInf_eq_false_of_arithIsZero hz] at h; cases h

theorem fma_arithIsInf_eq_false_of_isNaN (h : isNaN fmt a = true) : arithIsInf fmt a = false := by
  cases hi : arithIsInf fmt a
  · rfl
  · rw [isNaN_eq_false_of_arithIsInf hi] at h; cases h

theorem fma_arithIsZero_eq_false_of_isNaN (h : isNaN fmt a = true) : arithIsZero fmt a = false := by
  cases hz : arithIsZero fmt a
  · rfl
  · rw [div_isNaN_eq_false_of_arithIsZero hz] at h; cases h

/-- The invalid product of FloatLib is the product of a zero and an infinity of SoftFloat. -/
theorem fma_invalidProduct_eq (fmt : Format) (a b : Nat) :
    ((arithIsInf fmt a || arithIsInf fmt b) && (arithIsZero fmt a || arithIsZero fmt b)) =
      ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) := by
  have ea : arithIsInf fmt a = true → arithIsZero fmt a = false :=
    fma_arithIsZero_eq_false_of_arithIsInf
  have eb : arithIsInf fmt b = true → arithIsZero fmt b = false :=
    fma_arithIsZero_eq_false_of_arithIsInf
  cases ia : arithIsInf fmt a <;> cases za : arithIsZero fmt a <;>
    cases ib : arithIsInf fmt b <;> cases zb : arithIsZero fmt b <;> simp_all

/-! ## The NaN that FloatLib chooses for three operands -/

theorem fma_chooseNaN3 (op : NaNOperation) (hop : op ≠ .subtraction)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) (hc : c < 2 ^ fmt.width)
    (h : (isNaN fmt a || isNaN fmt b || isNaN fmt c) = true) :
    ∃ nan, Model.chooseNaN3 (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) = some nan ∧
      nan.toNatBits = floatLibNaN op fmt [(fmt, a), (fmt, b), (fmt, c)] := by
  have hi : ∀ i, ¬ (op = .subtraction ∧ i = 1) := fun _ hc => hop hc.1
  unfold Model.chooseNaN3 floatLibNaN
  simp only [firstNaN, model_isSNaN, model_isNaN, isSNaN_ofBits ha, isSNaN_ofBits hb,
    isSNaN_ofBits hc, isNaN_ofBits ha, isNaN_ofBits hb, isNaN_ofBits hc]
  have ia : isSignalingNaN fmt a = true → isNaN fmt a = true := isNaN_of_isSignalingNaN
  have ib : isSignalingNaN fmt b = true → isNaN fmt b = true := isNaN_of_isSignalingNaN
  have ic : isSignalingNaN fmt c = true → isNaN fmt c = true := isNaN_of_isSignalingNaN
  cases hsa : isSignalingNaN fmt a <;> cases hsb : isSignalingNaN fmt b <;>
    cases hsc : isSignalingNaN fmt c <;>
    cases hna : isNaN fmt a <;> cases hnb : isNaN fmt b <;> cases hnc : isNaN fmt c <;>
    simp only [hsa, hsb, hsc, hna, hnb, hnc, Bool.false_eq_true, ↓reduceIte, Option.orElse,
      Option.some.injEq, exists_eq_left', Bool.or_self, Bool.or_false, Bool.false_or] at ia ib ic h ⊢ <;>
    first
      | exact (floatLibNaN_of_nan ha hna op 0 (hi 0)).symm
      | exact (floatLibNaN_of_nan hb hnb op 1 (hi 1)).symm
      | exact (floatLibNaN_of_nan hc hnc op 2 (hi 2)).symm
      | simp at ia ib ic h

theorem fma_chooseNaN3_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hc : c < 2 ^ fmt.width) (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false)
    (hnc : isNaN fmt c = false) :
    Model.chooseNaN3 (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) = none := by
  unfold Model.chooseNaN3
  simp [model_isSNaN, model_isNaN, isSNaN_ofBits ha, isSNaN_ofBits hb, isSNaN_ofBits hc,
    isNaN_ofBits ha, isNaN_ofBits hb, isNaN_ofBits hc, hna, hnb, hnc,
    div_isSignalingNaN_eq_false hna, div_isSignalingNaN_eq_false hnb,
    div_isSignalingNaN_eq_false hnc]

theorem fma_floatLibNaN_no_nan (op : NaNOperation) (hna : isNaN fmt a = false)
    (hnb : isNaN fmt b = false) (hnc : isNaN fmt c = false) :
    floatLibNaN op fmt [(fmt, a), (fmt, b), (fmt, c)] = fmt.pack false fmt.expMax fmt.quietBit := by
  unfold floatLibNaN
  simp [firstNaN, hna, hnb, hnc, div_isSignalingNaN_eq_false hna, div_isSignalingNaN_eq_false hnb,
    div_isSignalingNaN_eq_false hnc, Option.orElse]
  rfl

/-! ## The outcome of the fused multiply-add of FloatLib -/

theorem flFma_fst (fmt : Format) (a b c : Nat) :
    (flFma fmt a b c).1 = (Model.Spec.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c)).toNatBits := by
  show (Model.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) (mode := .nearest)
    (status := true)).value.toNatBits = _
  rw [Model.value_fma, Model.Proof.fma_eq_spec]

/-- The invalid flag of FloatLib for a fused multiply-add with an operand that is a NaN or an
infinity. -/
def fmaInvalid (fmt : Format) (a b c : Nat) : Bool :=
  isSignalingNaN fmt a || isSignalingNaN fmt b || isSignalingNaN fmt c ||
    ((arithIsInf fmt a || arithIsInf fmt b) && (arithIsZero fmt a || arithIsZero fmt b)) ||
    (!(isNaN fmt a || isNaN fmt b || isNaN fmt c) &&
      ((arithIsInf fmt a || arithIsInf fmt b) && !(arithIsZero fmt a || arithIsZero fmt b) &&
        arithIsInf fmt c &&
        (fmt.unpack c).sign != Bool.xor (fmt.unpack a).sign (fmt.unpack b).sign))

theorem flFma_snd_of_none (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hc : c < 2 ^ fmt.width)
    (h : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none ∨
      Model.toDyadic? (ofBits fmt c) = none) :
    (flFma fmt a b c).2 = { invalidOperation := fmaInvalid fmt a b c } := by
  show flagsOf (Model.Internal.Status.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c)
    .nearest).status = _
  unfold Model.Internal.Status.fma
  split
  · rename_i hx hy hz
    rcases h with h | h | h <;> simp_all
  · dsimp only
    rw [flagsOf_outcomeWithInvalid, div_isSNaN_ofBits ha, div_isSNaN_ofBits hb, div_isSNaN_ofBits hc,
      div_isNaN_ofBits ha, div_isNaN_ofBits hb, div_isNaN_ofBits hc, isInf_ofBits' ha,
      isInf_ofBits' hb, isInf_ofBits' hc, div_isZero_ofBits ha, div_isZero_ofBits hb,
      signBit_ofBits ha, signBit_ofBits hb, signBit_ofBits hc]
    rfl

/-! ## Fused multiply-add when the specification does not round -/

/-- The condition under which `FusedMultiplyAddSpecOf` does not take its rounded branch: an
operand is a NaN or an infinity (the product of a zero and an infinity has an infinite factor).
Its complement is that the three operands are finite (neither a NaN nor an infinity). -/
def fmaExceptional (fmt : Format) (a b c : Nat) : Bool :=
  isNaN fmt a || isNaN fmt b || isNaN fmt c ||
    arithIsInf fmt a || arithIsInf fmt b || arithIsInf fmt c

/-- Outside `fmaExceptional`, `FusedMultiplyAddSpecOf` is its rounded branch. -/
theorem fusedMultiplyAddSpecOf_of_not_exceptional (sp : Specialization) (fmt dst : Format)
    (rm : RoundingDirection) (a b c : Nat) (r : Nat × StatusFlags)
    (hx : fmaExceptional fmt a b c = false) :
    FusedMultiplyAddSpecOf sp fmt fmt fmt dst rm a b c r ↔
      dst.IsEncoding r.1 ∧
        RoundedResultOf sp dst rm (valR fmt a * valR fmt b + valR fmt c)
          (arithZeroSumNegative rm (arithSign fmt a != arithSign fmt b) (arithSign fmt c)) r := by
  unfold fmaExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨⟨⟨hna, hnb⟩, hnc⟩, hia⟩, hib⟩, hic⟩ := hx
  unfold FusedMultiplyAddSpecOf
  simp [hna, hnb, hnc, hia, hib, hic]

theorem floatlib_fma_meets_spec_of_exceptional (sp : Specialization) (hc : FloatLibChoices sp)
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) (hc' : c < 2 ^ fmt.width)
    (hx : fmaExceptional fmt a b c = true) :
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt .roundTiesToEven a b c (flFma fmt a b c) := by
  have hnone : Model.toDyadic? (ofBits fmt a) = none ∨ Model.toDyadic? (ofBits fmt b) = none ∨
      Model.toDyadic? (ofBits fmt c) = none := by
    rw [toDyadic?_ofBits_eq_none_iff ha, toDyadic?_ofBits_eq_none_iff hb,
      toDyadic?_ofBits_eq_none_iff hc']
    unfold fmaExceptional at hx
    simp only [Bool.or_eq_true] at hx ⊢
    tauto
  have hia := isInf_ofBits' ha
  have hib := isInf_ofBits' hb
  have hic := isInf_ofBits' hc'
  have hza := div_isZero_ofBits ha
  have hzb := div_isZero_ofBits hb
  have hsa := signBit_ofBits ha
  have hsb := signBit_ofBits hb
  have hsc := signBit_ofBits hc'
  have hip := fma_invalidProduct_eq fmt a b
  unfold FusedMultiplyAddSpecOf
  refine ⟨by rw [flFma_fst]; exact isEncoding_toNatBits _, ?_⟩
  rw [hc.propagateNaN .fusedMultiplyAdd fmt _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), hc.fusedMultiplyAddZeroInfinityQuietNaNInvalid,
    flFma_snd_of_none ha hb hc' hnone, flFma_fst]
  unfold fmaInvalid
  rw [hip]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · -- A NaN factor: FloatLib delivers the NaN it chooses, quieted.
    obtain ⟨nan, hch, hbits⟩ := fma_chooseNaN3 .fusedMultiplyAdd (by decide) ha hb hc'
      (by simp only [Bool.or_eq_true] at h1 ⊢; tauto)
    unfold Model.Spec.fma
    rw [hch]
    refine ⟨hbits, ?_⟩
    have hz : ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) =
        false := by
      simp only [Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · simp [fma_arithIsInf_eq_false_of_isNaN h1, fma_arithIsZero_eq_false_of_isNaN h1]
      · simp [fma_arithIsInf_eq_false_of_isNaN h1, fma_arithIsZero_eq_false_of_isNaN h1]
    simp [h1, hz]
  · -- The addend is a NaN and the product is of a zero and an infinity: invalid.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    obtain ⟨nan, hch, hbits⟩ := fma_chooseNaN3 .fusedMultiplyAdd (by decide) ha hb hc'
      (by simp [h2])
    unfold Model.Spec.fma
    rw [hch]
    refine ⟨hbits, ?_⟩
    simp [h3, div_isSignalingNaN_eq_false hna, div_isSignalingNaN_eq_false hnb]
  · -- The addend is a NaN otherwise.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have h3' : ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) =
        false := by simpa using h3
    obtain ⟨nan, hch, hbits⟩ := fma_chooseNaN3 .fusedMultiplyAdd (by decide) ha hb hc'
      (by simp [h2])
    unfold Model.Spec.fma
    rw [hch]
    refine ⟨hbits, ?_⟩
    simp [h2, h3', div_isSignalingNaN_eq_false hna, div_isSignalingNaN_eq_false hnb]
  · -- The product of a zero and an infinity: the canonical NaN, and invalid.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hnc : isNaN fmt c = false := by simp_all
    rw [fma_floatLibNaN_no_nan .fusedMultiplyAdd hna hnb hnc]
    unfold Model.Spec.fma
    rw [fma_chooseNaN3_none ha hb hc' hna hnb hnc]
    have hinf : (Model.isInf (ofBits fmt a) || Model.isInf (ofBits fmt b)) = true := by
      rw [hia, hib]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h4 ⊢
      tauto
    have hzero : (Model.isZero (ofBits fmt a) || Model.isZero (ofBits fmt b)) = true := by
      rw [hza, hzb]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h4 ⊢
      tauto
    simp only [hinf, hzero, ↓reduceIte]
    rw [toNatBits_invalidResult]
    refine ⟨rfl, ?_⟩
    simp [h4]
  · -- An infinite factor and an infinite addend of the other sign: the canonical NaN, and invalid.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hnc : isNaN fmt c = false := by simp_all
    have hsa' := div_isSignalingNaN_eq_false hna
    have hsb' := div_isSignalingNaN_eq_false hnb
    have hsc' := div_isSignalingNaN_eq_false hnc
    have h4' : ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) =
        false := by simpa using h4
    have hzero : (arithIsZero fmt a || arithIsZero fmt b) = false := by
      have := hip.trans h4'
      rw [h5, Bool.true_and] at this
      exact this
    have hinf : (Model.isInf (ofBits fmt a) || Model.isInf (ofBits fmt b)) = true := by
      rw [hia, hib]; exact h5
    have hzero' : (Model.isZero (ofBits fmt a) || Model.isZero (ofBits fmt b)) = false := by
      rw [hza, hzb]; exact hzero
    have hsab' : (arithSign fmt a != arithSign fmt b) =
        Bool.xor (fmt.unpack a).sign (fmt.unpack b).sign := by
      rw [div_xor_eq_bne, div_arithSign_eq hna, div_arithSign_eq hnb]
    have hsab : (arithSign fmt a != arithSign fmt b) =
        Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b)) := by
      rw [hsab', hsa, hsb]
    unfold Model.Spec.fma
    rw [fma_chooseNaN3_none ha hb hc' hna hnb hnc]
    simp only [hinf, hzero', ↓reduceIte, Bool.false_eq_true]
    rw [fma_floatLibNaN_no_nan .fusedMultiplyAdd hna hnb hnc]
    simp only [Bool.and_eq_true] at h6
    obtain ⟨h6a, h6b⟩ := h6
    have hzc : Model.isInf (ofBits fmt c) = true := by rw [hic]; exact h6a
    have hsz : (Model.signBit (ofBits fmt c) !=
        Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b))) = true := by
      rw [← hsab, hsc, ← arithSign_of_arithIsInf h6a]; exact h6b
    have hsz' : ((fmt.unpack c).sign != Bool.xor (fmt.unpack a).sign (fmt.unpack b).sign) =
        true := by
      rw [← hsab', ← arithSign_of_arithIsInf h6a]; exact h6b
    simp only [hzc, hsz, ↓reduceIte]
    rw [toNatBits_invalidResult]
    refine ⟨rfl, ?_⟩
    simp [hna, hnb, hnc, hsa', hsb', hsc', h4', h5, hzero, h6a, hsz']
  · -- An infinite factor otherwise: an infinity of the sign of the product.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hnc : isNaN fmt c = false := by simp_all
    have hsa' := div_isSignalingNaN_eq_false hna
    have hsb' := div_isSignalingNaN_eq_false hnb
    have hsc' := div_isSignalingNaN_eq_false hnc
    have h4' : ((arithIsInf fmt a && arithIsZero fmt b) || (arithIsZero fmt a && arithIsInf fmt b)) =
        false := by simpa using h4
    have hzero : (arithIsZero fmt a || arithIsZero fmt b) = false := by
      have := hip.trans h4'
      rw [h5, Bool.true_and] at this
      exact this
    have hinf : (Model.isInf (ofBits fmt a) || Model.isInf (ofBits fmt b)) = true := by
      rw [hia, hib]; exact h5
    have hzero' : (Model.isZero (ofBits fmt a) || Model.isZero (ofBits fmt b)) = false := by
      rw [hza, hzb]; exact hzero
    have hsab' : (arithSign fmt a != arithSign fmt b) =
        Bool.xor (fmt.unpack a).sign (fmt.unpack b).sign := by
      rw [div_xor_eq_bne, div_arithSign_eq hna, div_arithSign_eq hnb]
    have hsab : (arithSign fmt a != arithSign fmt b) =
        Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b)) := by
      rw [hsab', hsa, hsb]
    unfold Model.Spec.fma
    rw [fma_chooseNaN3_none ha hb hc' hna hnb hnc]
    simp only [hinf, hzero', ↓reduceIte, Bool.false_eq_true]
    have hopp : (arithIsInf fmt c &&
        ((fmt.unpack c).sign != Bool.xor (fmt.unpack a).sign (fmt.unpack b).sign)) = false := by
      cases hic' : arithIsInf fmt c
      · rfl
      · rw [hic', arithSign_of_arithIsInf hic', hsab'] at h6
        simpa using h6
    have hval : classify fmt (if Model.isInf (ofBits fmt c) = true then
        if (Model.signBit (ofBits fmt c) !=
            Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b))) = true then
          Model.invalidResult (toFL fmt)
        else Model.nativeOverflow (toFL fmt)
          (Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b)))
      else Model.nativeOverflow (toFL fmt)
        (Bool.xor (Model.signBit (ofBits fmt a)) (Model.signBit (ofBits fmt b)))).toNatBits =
        .infinity (arithSign fmt a != arithSign fmt b) := by
      rw [hsab]
      split_ifs with h7' h8'
      · exfalso
        rw [hic] at h7'
        rw [hsc, hsa, hsb] at h8'
        rw [h7', h8'] at hopp
        simp at hopp
      · exact div_classify_nativeOverflow _
      · exact div_classify_nativeOverflow _
    refine ⟨hval, ?_⟩
    cases hic' : arithIsInf fmt c
    · simp [hna, hnb, hnc, hsa', hsb', hsc', h4']
    · rw [hic'] at hopp
      simp only [Bool.true_and] at hopp
      simp [hna, hnb, hnc, hsa', hsb', hsc', h4', hopp]
  · -- An infinite addend and finite factors: the addend is delivered.
    have hna : isNaN fmt a = false := by simp_all
    have hnb : isNaN fmt b = false := by simp_all
    have hnc : isNaN fmt c = false := by simp_all
    have hfab : (arithIsInf fmt a || arithIsInf fmt b) = false := by simpa using h5
    have hinf : (Model.isInf (ofBits fmt a) || Model.isInf (ofBits fmt b)) = false := by
      rw [hia, hib]; exact hfab
    have hfa : arithIsInf fmt a = false := by simp_all
    have hfb : arithIsInf fmt b = false := by simp_all
    unfold Model.Spec.fma
    rw [fma_chooseNaN3_none ha hb hc' hna hnb hnc]
    simp only [hinf, hic, h7, ↓reduceIte, Bool.false_eq_true]
    rw [toNatBits_ofBits hc', classify_of_arithIsInf h7]
    refine ⟨rfl, ?_⟩
    simp [hna, hnb, hnc, div_isSignalingNaN_eq_false hna, div_isSignalingNaN_eq_false hnb,
      div_isSignalingNaN_eq_false hnc, hfa, hfb]
  · -- Otherwise the specification rounds, against the hypothesis.
    unfold fmaExceptional at hx
    simp_all

end SoftFloat.FloatLib.Proof
