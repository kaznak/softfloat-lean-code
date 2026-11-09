/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Bits
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Exceptional values of FloatLib as bit strings of SoftFloat

The canonical NaN, a quieted NaN, and the test of FloatLib for an operand that is not finite,
in the terms of SoftFloat.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {a : Nat}

theorem isEncoding_toNatBits (x : Model (toFL fmt)) : fmt.IsEncoding x.toNatBits := by
  have := x.toNatBits_lt_two_pow
  rwa [bitWidth_toFL] at this

theorem toNatBits_canonicalNaN (fmt : Format) :
    (Model.canonicalNaN (toFL fmt)).toNatBits = fmt.pack false fmt.expMax fmt.quietBit := by
  have hq : 2 ^ (fmt.fracBits - 1) < 2 ^ fmt.fracBits := quietBit_lt fmt
  have hlt1 : FloatFormat.expAllOnesNat (toFL fmt) * 2 ^ (toFL fmt).fracWidth < 2 ^ (toFL fmt).bitWidth := by
    rw [bitWidth_toFL, expAllOnesNat_toFL, fracWidth_toFL]
    have := pack_lt fmt false (expMax_lt fmt) (Nat.two_pow_pos fmt.fracBits)
    unfold Format.pack at this
    have h0 := pack_lt fmt false (e := fmt.expMax) (f := 0) (expMax_lt fmt) (Nat.two_pow_pos _)
    unfold Format.pack at h0
    simpa using h0
  have hlt2 : 2 ^ ((toFL fmt).fracWidth - 1) < 2 ^ (toFL fmt).bitWidth := by
    rw [bitWidth_toFL, fracWidth_toFL]
    have h0 := pack_lt fmt false (e := 0) (Nat.two_pow_pos fmt.expBits) hq
    unfold Format.pack at h0
    simpa using h0
  unfold Model.canonicalNaN Model.toNatBits Model.ofBits FloatFormat.expMask FloatFormat.quietBit
    FloatFormat.ofWordNat FloatFormat.expMaskNat FloatFormat.quietBitNat
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
    Nat.mod_eq_of_lt hlt2, expAllOnesNat_toFL, fracWidth_toFL]
  unfold Format.pack Format.quietBit
  have key := Nat.two_pow_add_eq_or_of_lt hq fmt.expMax
  rw [Nat.mul_comm (2 ^ fmt.fracBits) fmt.expMax] at key
  simpa using key.symm

theorem toNatBits_invalidResult (fmt : Format) :
    (Model.invalidResult (toFL fmt)).toNatBits = fmt.pack false fmt.expMax fmt.quietBit :=
  toNatBits_canonicalNaN fmt

theorem expField_eq_expMax_of_isNaN (hn : isNaN fmt a = true) :
    (fmt.unpack a).expField = fmt.expMax := by
  rw [← isNaNU_unpack] at hn
  unfold Format.isNaNU at hn
  simp only [Bool.and_eq_true, beq_iff_eq] at hn
  exact hn.1

/-- A NaN of SoftFloat, quieted by FloatLib: the quiet bit is set, and the sign and the rest of
the fraction field are kept. -/
theorem toNatBits_quietNaN (ha : a < 2 ^ fmt.width) (hn : isNaN fmt a = true) :
    (Model.quietNaN (ofBits fmt a)).toNatBits =
      fmt.pack (fmt.unpack a).sign fmt.expMax (fmt.quietBit + (fmt.unpack a).fracField % fmt.quietBit) := by
  have hx : Model.ofBits (ofBits fmt a).bits = ofBits fmt a := rfl
  have hq : Model.IEEE.isNaN (ofBits fmt a) = true := by rw [isNaN_ofBits ha]; exact hn
  show (if Model.IEEE.isNaN (ofBits fmt a) then
      Model.ofBits ((ofBits fmt a).bits ||| FloatFormat.quietBit (toFL fmt)) else ofBits fmt a).toNatBits = _
  rw [ite_eq_left_of_eq_true _ _ (eq_true hq), toNatBits_eq_pack, Model.signBit_or_quietBit, Model.expField_or_quietBit,
    Model.fracField_or_quietBit, hx, signBit_ofBits ha, expField_ofBits ha, fracField_ofBits ha,
    expField_eq_expMax_of_isNaN hn, fracWidth_toFL]
  have hf : (fmt.unpack a).fracField < 2 ^ (fmt.fracBits - 1 + 1) := by
    rw [Nat.sub_add_cancel (one_le_fracBits fmt)]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [or_two_pow_eq hf]
  rfl

/-- FloatLib decodes an operand exactly unless it is a NaN or an infinity. -/
theorem toDyadic?_ofBits_eq_none_iff (ha : a < 2 ^ fmt.width) :
    Model.toDyadic? (ofBits fmt a) = none ↔ (isNaN fmt a || arithIsInf fmt a) = true := by
  have h := Model.toDyadic?_isSome_eq_isFinite (ofBits fmt a)
  rw [model_isFinite, isFinite_ofBits ha] at h
  rw [← Option.not_isSome_iff_eq_none, h, ← isNaNU_unpack, arithIsInf_eq]
  unfold Format.isNaNU Format.isInfU
  by_cases he : (fmt.unpack a).expField = fmt.expMax <;>
    by_cases hf : (fmt.unpack a).fracField = 0 <;> simp [he, hf]

end SoftFloat.FloatLib.Proof
