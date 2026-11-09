/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Encoding
import SoftFloat.FloatLib.Spec.Ops
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Proof

/-!
# The bit strings of SoftFloat and the values of FloatLib

A value of FloatLib in the format `toFL fmt` is a bit vector of the width of `fmt`. Its fields,
read by FloatLib with shifts and masks, are the fields that `Format.unpack` reads with division
and remainder, and its classification is the classification of SoftFloat.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

/-! ## The format -/

theorem expWidth_toFL (fmt : Format) : (toFL fmt).expWidth = fmt.expBits := rfl

theorem fracWidth_toFL (fmt : Format) : (toFL fmt).fracWidth = fmt.fracBits := rfl

theorem bitWidth_toFL (fmt : Format) : (toFL fmt).bitWidth = fmt.width := by
  unfold FloatFormat.bitWidth Format.width
  rw [expWidth_toFL, fracWidth_toFL]
  have := fmt.sigBits_three_le
  unfold Format.fracBits
  omega

theorem expAllOnesNat_toFL (fmt : Format) : FloatFormat.expAllOnesNat (toFL fmt) = fmt.expMax := rfl

/-! ## The fields of a value of FloatLib, as natural numbers -/

theorem fracField_eq {F : FloatFormat} (x : Model F) :
    Model.fracField x = x.toNatBits % 2 ^ F.fracWidth := by
  unfold Model.fracField FloatFormat.fracMask FloatFormat.ofWordNat FloatFormat.fracMaskNat
    Model.toNatBits
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hmask : 2 ^ F.fracWidth - 1 < 2 ^ F.bitWidth := by
    have : 2 ^ F.fracWidth ≤ 2 ^ F.bitWidth :=
      Nat.pow_le_pow_right (by decide) (by unfold FloatFormat.bitWidth; omega)
    have := Nat.one_le_two_pow (n := F.fracWidth)
    omega
  rw [Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod]

theorem expField_eq {F : FloatFormat} (x : Model F) :
    Model.expField x = x.toNatBits / 2 ^ F.fracWidth % 2 ^ F.expWidth := by
  unfold Model.expField FloatFormat.expAllOnes FloatFormat.ofWordNat FloatFormat.expAllOnesNat
    Model.toNatBits
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  have hmask : 2 ^ F.expWidth - 1 < 2 ^ F.bitWidth := by
    have : 2 ^ F.expWidth ≤ 2 ^ F.bitWidth :=
      Nat.pow_le_pow_right (by decide) (by unfold FloatFormat.bitWidth; omega)
    have := Nat.one_le_two_pow (n := F.expWidth)
    omega
  rw [Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem signBit_eq {F : FloatFormat} (x : Model F) :
    Model.signBit x = (x.toNatBits / 2 ^ (F.bitWidth - 1) % 2 == 1) := by
  rw [Model.signBit_eq_msb, BitVec.msb_eq_decide]
  have hlt : x.toNatBits < 2 ^ F.bitWidth := x.toNatBits_lt_two_pow
  have hw : 2 ^ F.bitWidth = 2 * 2 ^ (F.bitWidth - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    unfold FloatFormat.bitWidth
    omega
  have hp : 0 < 2 ^ (F.bitWidth - 1) := Nat.two_pow_pos _
  have hq : x.toNatBits / 2 ^ (F.bitWidth - 1) < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  have hle : 1 ≤ x.toNatBits / 2 ^ (F.bitWidth - 1) ↔ 1 * 2 ^ (F.bitWidth - 1) ≤ x.toNatBits :=
    Nat.le_div_iff_mul_le hp
  change decide (2 ^ (F.bitWidth - 1) ≤ x.toNatBits) = _
  by_cases h : 2 ^ (F.bitWidth - 1) ≤ x.toNatBits
  · have h1 : x.toNatBits / 2 ^ (F.bitWidth - 1) = 1 := by omega
    simp [h, h1]
  · have h0 : x.toNatBits / 2 ^ (F.bitWidth - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, h0]

/-! ## A bit string of SoftFloat as a value of FloatLib -/

variable {fmt : Format} {a : Nat}

theorem toNatBits_ofBits (ha : a < 2 ^ fmt.width) : (ofBits fmt a).toNatBits = a :=
  Model.toNatBits_ofNatBits_of_lt a (by rw [bitWidth_toFL]; exact ha)

theorem fracField_ofBits (ha : a < 2 ^ fmt.width) :
    Model.fracField (ofBits fmt a) = (fmt.unpack a).fracField := by
  rw [fracField_eq, toNatBits_ofBits ha]
  rfl

theorem expField_ofBits (ha : a < 2 ^ fmt.width) :
    Model.expField (ofBits fmt a) = (fmt.unpack a).expField := by
  rw [expField_eq, toNatBits_ofBits ha]
  rfl

theorem signBit_ofBits (ha : a < 2 ^ fmt.width) :
    Model.signBit (ofBits fmt a) = (fmt.unpack a).sign := by
  rw [signBit_eq, toNatBits_ofBits ha, bitWidth_toFL]
  rfl

/-! ## The classification -/

theorem isNaN_ofBits (ha : a < 2 ^ fmt.width) :
    Model.IEEE.isNaN (ofBits fmt a) = isNaN fmt a := by
  rw [← isNaNU_unpack]
  unfold Model.IEEE.isNaN Format.isNaNU
  rw [expField_ofBits ha, fracField_ofBits ha, expAllOnesNat_toFL]

theorem isInf_ofBits (ha : a < 2 ^ fmt.width) :
    Model.IEEE.isInf (ofBits fmt a) = fmt.isInfU (fmt.unpack a) := by
  unfold Model.IEEE.isInf Format.isInfU
  rw [expField_ofBits ha, fracField_ofBits ha, expAllOnesNat_toFL]

theorem isZero_ofBits (ha : a < 2 ^ fmt.width) :
    Model.IEEE.isZero (ofBits fmt a) = Format.isZeroU (fmt.unpack a) := by
  unfold Model.IEEE.isZero Format.isZeroU
  rw [expField_ofBits ha, fracField_ofBits ha]

theorem isFinite_ofBits (ha : a < 2 ^ fmt.width) :
    Model.IEEE.isFinite (ofBits fmt a) = ((fmt.unpack a).expField != fmt.expMax) := by
  unfold Model.IEEE.isFinite
  rw [expField_ofBits ha, expAllOnesNat_toFL]

/-! The classification of FloatLib in an IEEE format, which `toFL` always is. -/

theorem model_isNaN (x : Model (toFL fmt)) : Model.isNaN x = Model.IEEE.isNaN x := rfl
theorem model_isSNaN (x : Model (toFL fmt)) : Model.isSNaN x = Model.IEEE.isSNaN x := rfl
theorem model_isInf (x : Model (toFL fmt)) : Model.isInf x = Model.IEEE.isInf x := rfl
theorem model_isZero (x : Model (toFL fmt)) : Model.isZero x = Model.IEEE.isZero x := rfl
theorem model_isFinite (x : Model (toFL fmt)) : Model.isFinite x = Model.IEEE.isFinite x := rfl

/-! ## The classification of SoftFloat, by the fields -/

theorem arithIsInf_eq (fmt : Format) (a : Nat) : arithIsInf fmt a = fmt.isInfU (fmt.unpack a) := by
  unfold arithIsInf Format.isInfU
  rw [classify_eq_fields]
  dsimp only
  by_cases he : (fmt.unpack a).expField = fmt.expMax <;> by_cases hf : (fmt.unpack a).fracField = 0 <;>
    simp [he, hf] <;> split_ifs <;> simp_all

theorem arithSign_of_arithIsInf {fmt : Format} {a : Nat} (h : arithIsInf fmt a = true) :
    arithSign fmt a = (fmt.unpack a).sign := by
  unfold arithIsInf at h
  unfold arithSign
  split <;> simp_all
  all_goals
    rename_i hc
    rw [classify_eq_fields] at hc
    dsimp only at hc
    split_ifs at hc
    simp_all

/-- A fraction field below `2 ^ f` has bit `f - 1` exactly when it is at least `2 ^ (f - 1)`. -/
theorem testBit_pred_eq {m f : Nat} (hm : m < 2 ^ f) (hf : 1 ≤ f) :
    m.testBit (f - 1) = decide (2 ^ (f - 1) ≤ m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hw : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hp : 0 < 2 ^ (f - 1) := Nat.two_pow_pos _
  have hq : m / 2 ^ (f - 1) < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
  by_cases h : 2 ^ (f - 1) ≤ m
  · have h1 : m / 2 ^ (f - 1) = 1 := by
      have : 1 ≤ m / 2 ^ (f - 1) := (Nat.le_div_iff_mul_le hp).2 (by rw [Nat.one_mul]; exact h)
      omega
    simp [h, h1]
  · have h0 : m / 2 ^ (f - 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, h0]

theorem isSNaN_ofBits (ha : a < 2 ^ fmt.width) :
    Model.IEEE.isSNaN (ofBits fmt a) = isSignalingNaN fmt a := by
  rw [← isSNaNU_unpack]
  unfold Model.IEEE.isSNaN Format.isSNaNU
  rw [isNaN_ofBits ha, ← isNaNU_unpack, Model.and_quietBit_eq_zero_iff, fracField_ofBits ha,
    fracWidth_toFL, testBit_pred_eq
      (show (fmt.unpack a).fracField < 2 ^ fmt.fracBits from Nat.mod_lt _ (Nat.two_pow_pos _))
      (one_le_fracBits fmt)]
  unfold Format.quietBit
  by_cases h : 2 ^ (fmt.fracBits - 1) ≤ (fmt.unpack a).fracField
  · simp [h]
  · simp [h]; omega

/-! ## The bit string of a value of FloatLib, from its fields -/

theorem toNatBits_eq_pack (x : Model (toFL fmt)) :
    x.toNatBits = fmt.pack (Model.signBit x) (Model.expField x) (Model.fracField x) := by
  have hlt : x.toNatBits < 2 ^ fmt.width := by
    have := x.toNatBits_lt_two_pow
    rwa [bitWidth_toFL] at this
  rw [fracField_eq, expField_eq, signBit_eq, bitWidth_toFL]
  exact (pack_unpack fmt hlt).symm

/-- Setting bit `k` of a number below `2 ^ (k + 1)` adds `2 ^ k` to its remainder by `2 ^ k`. -/
theorem or_two_pow_eq {m k : Nat} (hm : m < 2 ^ (k + 1)) : m ||| 2 ^ k = 2 ^ k + m % 2 ^ k := by
  have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
  have := Nat.two_pow_add_eq_or_of_lt hr 1
  rw [Nat.mul_one] at this
  rw [this]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < k
  · have : ¬ k = j := by omega
    simp [hj, this]
  · by_cases hk : k = j
    · subst hk; simp
    · have hlt : m < 2 ^ j := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
      simp [hj, hk, Nat.testBit_lt_two_pow hlt]

end SoftFloat.FloatLib.Proof
