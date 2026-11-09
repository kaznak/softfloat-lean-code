/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Fma
import SoftFloat.FloatLib.Proof.AddFinite

/-!
# Fused multiply-add of FloatLib against the specification of SoftFloat: finite operands

With the three operands finite, the public fused multiply-add of FloatLib rounds the exact dyadic
`x * y + z` once, to nearest with ties to even, and reports the status of that rounding. It meets
`FusedMultiplyAddSpecOf` for every specialization with the choices of FloatLib.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

/-- The exact dyadic product that FloatLib forms for a fused multiply-add. -/
def fmaF_product (dx dy : Dyadic) : Dyadic :=
  { negative := Bool.xor dx.negative dy.negative
    significand := dx.significand * dy.significand
    exponent := dx.exponent + dy.exponent }

theorem fmaF_toReal_product (dx dy : Dyadic) :
    (fmaF_product dx dy).toReal = dx.toReal * dy.toReal :=
  Model.Dyadic.toReal_mul dx dy

variable {fmt : Format} {a b c : Nat}

/-- The fused multiply-add of FloatLib on three finite operands: the rounded exact value and the
status of the rounding. -/
theorem fmaF_flFma_of_toDyadic {dx dy dz : Dyadic}
    (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width) (hc : c < 2 ^ fmt.width)
    (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false) (hnc : isNaN fmt c = false)
    (hia : arithIsInf fmt a = false) (hib : arithIsInf fmt b = false)
    (hic : arithIsInf fmt c = false)
    (hx : Model.toDyadic? (ofBits fmt a) = some dx)
    (hy : Model.toDyadic? (ofBits fmt b) = some dy)
    (hz : Model.toDyadic? (ofBits fmt c) = some dz) :
    flFma fmt a b c =
      ((Model.roundDyadic (toFL fmt) (Model.addDyadic (fmaF_product dx dy) dz)).toNatBits,
        flagsOf (Model.dyadicRoundingStatus (toFL fmt) .nearest
          (Model.addDyadic (fmaF_product dx dy) dz)
          (Model.roundDyadic (toFL fmt) (Model.addDyadic (fmaF_product dx dy) dz)))) := by
  have hv : Model.Spec.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) =
      Model.roundDyadic (toFL fmt) (Model.addDyadic (fmaF_product dx dy) dz) := by
    unfold Model.Spec.fma
    rw [fma_chooseNaN3_none ha hb hc hna hnb hnc, isInf_ofBits' ha, isInf_ofBits' hb,
      isInf_ofBits' hc, hia, hib, hic]
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    rw [hx, hy, hz]
    rfl
  have hst := Model.fma_status_of_toDyadic (x := ofBits fmt a) (y := ofBits fmt b)
    (z := ofBits fmt c) .nearest hx hy hz
  rw [Model.Proof.fma_eq_spec, hv] at hst
  show ofOutcome (Model.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) (mode := .nearest)
    (status := true)) = _
  rw [hst]
  rfl

/-- The fused multiply-add of FloatLib meets the specification of SoftFloat when the three
operands are finite. -/
theorem floatlib_fma_meets_spec_of_finite (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b c : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hc' : c < 2 ^ fmt.width) (hx : fmaExceptional fmt a b c = false) :
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt .roundTiesToEven a b c (flFma fmt a b c) := by
  rw [fusedMultiplyAddSpecOf_of_not_exceptional sp fmt fmt .roundTiesToEven a b c _ hx]
  unfold fmaExceptional at hx
  simp only [Bool.or_eq_false_iff] at hx
  obtain ⟨⟨⟨⟨⟨hna, hnb⟩, hnc⟩, hia⟩, hib⟩, hic⟩ := hx
  have hfa : IsFinite fmt a :=
    isFinite_of_not_isNaN_not_isInfU fmt hna (by rw [← arithIsInf_eq]; exact hia)
  have hfb : IsFinite fmt b :=
    isFinite_of_not_isNaN_not_isInfU fmt hnb (by rw [← arithIsInf_eq]; exact hib)
  have hfc : IsFinite fmt c :=
    isFinite_of_not_isNaN_not_isInfU fmt hnc (by rw [← arithIsInf_eq]; exact hic)
  set dx := decodeU fmt (fmt.unpack a)
  set dy := decodeU fmt (fmt.unpack b)
  set dz := decodeU fmt (fmt.unpack c)
  set d := Model.addDyadic (fmaF_product dx dy) dz
  have hval : d.toReal = valR fmt a * valR fmt b + valR fmt c := by
    rw [Model.Dyadic.toReal_addDyadic, fmaF_toReal_product, toReal_decodeU hfa,
      toReal_decodeU hfb, toReal_decodeU hfc]
  have hzero : d.significand = 0 →
      d.negative = arithZeroSumNegative .roundTiesToEven
        (arithSign fmt a != arithSign fmt b) (arithSign fmt c) := by
    intro h0
    rw [addDyadic_negative_of_significand_eq_zero _ dz h0, arithZeroSumNegative_roundTiesToEven,
      arithSign_eq fmt hna, arithSign_eq fmt hnb, arithSign_eq fmt hnc, decodeU_negative]
    show (Bool.xor dx.negative dy.negative && _) = _
    rw [decodeU_negative, decodeU_negative]
  have hmeets := roundDyadic_meets (fmt := fmt) sp hc.tininess d _ hzero
  rw [hval] at hmeets
  rw [fmaF_flFma_of_toDyadic ha hb hc' hna hnb hnc hia hib hic (toDyadic?_ofBits ha hfa)
    (toDyadic?_ofBits hb hfb) (toDyadic?_ofBits hc' hfc)]
  exact ⟨isEncoding_toNatBits _, hmeets⟩

-- ANCHOR: FloatLibFmaMeetsSpec
/-- The fused multiply-add of FloatLib meets the specification of fused multiply-add of Core on
every triple of bit strings of a format. -/
theorem floatlib_fma_meets_spec (sp : Specialization) (hc : FloatLibChoices sp)
    {fmt : Format} {a b c : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hc' : c < 2 ^ fmt.width) :
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt .roundTiesToEven a b c (flFma fmt a b c) := by
  cases h : fmaExceptional fmt a b c
  · exact floatlib_fma_meets_spec_of_finite sp hc ha hb hc' h
  · exact floatlib_fma_meets_spec_of_exceptional sp hc ha hb hc' h
-- ANCHOR_END: FloatLibFmaMeetsSpec

end SoftFloat.FloatLib.Proof
