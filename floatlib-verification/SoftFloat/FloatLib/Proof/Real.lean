/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Values
import SoftFloat.Core.Proof.Common
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# The real values of FloatLib and of SoftFloat

A finite bit string decodes in FloatLib to the dyadic whose real value is `valR`, and the
rounding of FloatLib to nearest with ties to even is `roundR` with `roundTiesToEven`.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

variable {fmt : Format} {n : Nat}

/-! ## The format -/

theorem isIEEE_toFL (fmt : Format) : (toFL fmt).isIEEE = true := by
  unfold toFL
  exact FloatFormat.isIEEE_ieee _ _ _ _

theorem bias_toFL (fmt : Format) : (toFL fmt).bias = fmt.bias := rfl

theorem exponentBias_toFL (fmt : Format) : (toFL fmt).exponentBias = fmt.bias := rfl

theorem minSubnormalExponent_toFL (fmt : Format) :
    (toFL fmt).minSubnormalExponent = fmt.minQ := by
  unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent Format.minQ
  rw [exponentBias_toFL, fracWidth_toFL]
  simp only [Int.ofNat_eq_natCast]

theorem ieeeMinSubnormalExponent_toFL (fmt : Format) :
    FloatFormat.ieeeMinSubnormalExponent (toFL fmt) = fmt.minQ := by
  unfold FloatFormat.ieeeMinSubnormalExponent Format.minQ
  rw [bias_toFL, fracWidth_toFL]
  simp only [Int.ofNat_eq_natCast]

theorem maxNormalExponent_toFL (fmt : Format) :
    (toFL fmt).maxNormalExponent = (fmt.bias : Int) := by
  rw [FloatFormat.maxNormalExponent_eq_ieee _ (isIEEE_toFL fmt)]
  rfl

/-! ## The fields of a value of FloatLib as the fields of its bit string -/

theorem unpack_toNatBits (v : Model (toFL fmt)) :
    fmt.unpack v.toNatBits = ⟨Model.signBit v, Model.expField v, Model.fracField v⟩ := by
  rw [fracField_eq, expField_eq, signBit_eq, bitWidth_toFL]
  rfl

theorem toNatBits_lt (v : Model (toFL fmt)) : v.toNatBits < 2 ^ fmt.width := by
  have := v.toNatBits_lt_two_pow
  rwa [bitWidth_toFL] at this

theorem ofBits_toNatBits (v : Model (toFL fmt)) : ofBits fmt v.toNatBits = v :=
  Model.ofNatBits_toNatBits v

theorem isFinite_toNatBits {v : Model (toFL fmt)} (h : Model.isFinite v = true) :
    IsFinite fmt v.toNatBits := by
  rw [isFinite_iff, unpack_toNatBits]
  rw [model_isFinite] at h
  unfold Model.IEEE.isFinite at h
  simpa [expAllOnesNat_toFL] using h

theorem classify_toNatBits_of_isInf {v : Model (toFL fmt)} (h : Model.isInf v = true) :
    classify fmt v.toNatBits = .infinity (Model.signBit v) := by
  rw [model_isInf] at h
  unfold Model.IEEE.isInf at h
  simp only [Bool.and_eq_true, beq_iff_eq, expAllOnesNat_toFL] at h
  rw [classify_eq_fields, unpack_toNatBits]
  simp [h.1, h.2]

/-! ## Decoding a finite bit string -/

/-- The dyadic that FloatLib decodes from the fields `u` of a finite bit string. -/
def decodeU (fmt : Format) (u : Format.Unpacked) : _root_.FloatLib.Numerics.Dyadic :=
  if u.expField = 0 then
    if u.fracField = 0 then ⟨u.sign, 0, 0⟩ else ⟨u.sign, u.fracField, fmt.minQ⟩
  else ⟨u.sign, 2 ^ fmt.fracBits + u.fracField, (u.expField : Int) - fmt.bias - fmt.fracBits⟩

theorem toDyadic?_ofBits (hn : n < 2 ^ fmt.width) (hf : IsFinite fmt n) :
    Model.toDyadic? (ofBits fmt n) = some (decodeU fmt (fmt.unpack n)) := by
  rw [isFinite_iff] at hf
  have hnan : Model.IEEE.isNaN (ofBits fmt n) = false := by
    unfold Model.IEEE.isNaN
    rw [expField_ofBits hn, expAllOnesNat_toFL]
    simp [hf]
  have hinf : Model.IEEE.isInf (ofBits fmt n) = false := by
    unfold Model.IEEE.isInf
    rw [expField_ofBits hn, expAllOnesNat_toFL]
    simp [hf]
  unfold Model.toDyadic?
  simp only [isIEEE_toFL, ↓reduceIte]
  unfold Model.ieeeToDyadic?
  rw [hnan, hinf]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [signBit_ofBits hn, expField_ofBits hn, fracField_ofBits hn]
  unfold decodeU
  by_cases he : (fmt.unpack n).expField = 0
  · by_cases hz : (fmt.unpack n).fracField = 0
    · simp [he, hz]
    · simp only [he, hz, beq_iff_eq, ↓reduceIte]
      rw [ieeeMinSubnormalExponent_toFL]
  · simp only [he, beq_iff_eq, ↓reduceIte, Option.some.injEq]
    rw [Model.pow2_eq_two_pow, fracWidth_toFL]
    congr 1
    unfold FloatFormat.ieeeNormalMantissaExpOffset
    rw [bias_toFL, fracWidth_toFL]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    ring

theorem decodeU_negative (fmt : Format) (u : Format.Unpacked) :
    (decodeU fmt u).negative = u.sign := by
  unfold decodeU
  split_ifs <;> rfl

theorem decodeU_significand (fmt : Format) (u : Format.Unpacked) :
    (decodeU fmt u).significand = fmt.sigOf u := by
  unfold decodeU Format.sigOf
  split_ifs <;> simp_all

theorem toReal_decodeU (hf : IsFinite fmt n) :
    (decodeU fmt (fmt.unpack n)).toReal = valR fmt n := by
  rw [valR_eq_sigOf fmt hf]
  unfold decodeU Format.sigOf Format.ulpExpOf
  simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
    _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand]
  by_cases he : (fmt.unpack n).expField = 0
  · by_cases hz : (fmt.unpack n).fracField = 0
    · simp [he, hz]
    · simp only [he, hz, ↓reduceIte]
      unfold Format.minQ
      ring_nf
  · simp only [he, ↓reduceIte]

theorem toReal_ofBits (hn : n < 2 ^ fmt.width) (hf : IsFinite fmt n) :
    Model.toReal (ofBits fmt n) = valR fmt n := by
  rw [Model.toReal_eq, toDyadic?_ofBits hn hf]
  exact toReal_decodeU hf

theorem valR_toNatBits {v : Model (toFL fmt)} (h : Model.isFinite v = true) :
    valR fmt v.toNatBits = Model.toReal v := by
  rw [← toReal_ofBits (toNatBits_lt v) (isFinite_toNatBits h), ofBits_toNatBits]


/-! ## Rounding to nearest with ties to even -/

open _root_.FloatLib.Floats.Formats.Flocq (nearestEven) in
theorem nearestEven_eq (y : ℝ) : nearestEven y = roundMagTiesToEven y := by
  unfold nearestEven roundMagTiesToEven
  simp only [Int.even_iff, gt_iff_lt]

theorem bpow_binary (e : Int) :
    _root_.FloatLib.Floats.Formats.Flocq.bpow _root_.FloatLib.Numerics.binaryRadix e = (2 : ℝ) ^ e := by
  norm_num [_root_.FloatLib.Floats.Formats.Flocq.bpow, _root_.FloatLib.Numerics.binaryRadix,
    _root_.FloatLib.Numerics.Radix.toReal]

theorem roundMagTiesToEven_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ roundMagTiesToEven y := by
  have := ceil_sub_half_le_roundMagTiesToEven y
  have : (-1 : ℤ) < ⌈y - 1 / 2⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- Rounding to nearest with ties to even in FloatLib is `roundR` with `roundTiesToEven`. -/
theorem roundR_eq_roundAt (fmt : Format) (x : ℝ) :
    roundR fmt .roundTiesToEven x = Model.roundAt (toFL fmt) x := by
  by_cases hx : x = 0
  · rw [hx, roundR_zero, Model.roundAt_zero]
  have hc : _root_.FloatLib.Floats.Formats.Flocq.cexp _root_.FloatLib.Numerics.binaryRadix
      (Model.fexpOf (toFL fmt)) x = cexpR fmt x := by
    unfold _root_.FloatLib.Floats.Formats.Flocq.cexp Model.fexpOf
      _root_.FloatLib.Floats.Formats.Flocq.fltExp cexpR magR
    rw [_root_.FloatLib.Floats.Formats.Flocq.magnitude_eq_int_log_add_one _ _ hx,
      minSubnormalExponent_toFL, fracWidth_toFL]
    have := sigBits_eq_fracBits_add_one fmt
    simp only [_root_.FloatLib.Numerics.binaryRadix]
    congr 1
    omega
  show _ = _root_.FloatLib.Floats.Formats.Flocq.round (β := _root_.FloatLib.Numerics.binaryRadix)
    (fexp := Model.fexpOf (toFL fmt)) _root_.FloatLib.Floats.Formats.Flocq.nearestEven x
  unfold _root_.FloatLib.Floats.Formats.Flocq.round
    _root_.FloatLib.Floats.Formats.Flocq.scaledMantissa
    _root_.FloatLib.Floats.Formats.Flocq.toReal
  simp only [hc, bpow_binary]
  unfold roundR roundAbs
  dsimp only
  rw [zpow_neg, ← div_eq_mul_inv]
  by_cases hneg : x < 0
  · have hab : x / (2 : ℝ) ^ cexpR fmt x = -(|x| / 2 ^ cexpR fmt x) := by
      rw [abs_of_neg hneg]; ring
    rw [hab, _root_.FloatLib.Floats.Formats.BinaryInterchange.Model.nearestEven_neg, nearestEven_eq]
    simp only [hneg, ↓reduceIte]
    push_cast
    ring
  · rw [abs_of_nonneg (not_lt.mp hneg), nearestEven_eq]
    simp only [hneg, ↓reduceIte, one_mul]

/-- Rounding to nearest with ties to even is below an even integer `N` exactly when the value is
below `N - 1 / 2`. -/
theorem roundMagTiesToEven_lt_iff {N : ℤ} (hN : N % 2 = 0) (y : ℝ) :
    roundMagTiesToEven y < N ↔ y < N - 1 / 2 := by
  constructor
  · intro h
    by_contra hy
    rcases lt_or_eq_of_le (not_lt.mp hy) with hy | hy
    · have h1 := ceil_sub_half_le_roundMagTiesToEven y
      have : N ≤ ⌈y - 1 / 2⌉ := Int.le_ceil_iff.mpr (by linarith)
      omega
    · have hfl : ⌊y⌋ = N - 1 := by
        rw [Int.floor_eq_iff, ← hy]; push_cast; constructor <;> linarith
      have hfr : y - ((N - 1 : ℤ) : ℝ) = 1 / 2 := by rw [← hy]; push_cast; ring
      unfold roundMagTiesToEven at h
      simp only [hfl, hfr, lt_self_iff_false, ↓reduceIte] at h
      split_ifs at h <;> omega
  · intro h
    have h1 := roundMagTiesToEven_le_floor_add_half y
    have : ⌊y + 1 / 2⌋ < N := Int.floor_lt.mpr (by linarith)
    omega

/-- Rounding to nearest is at least an integer below the value. -/
theorem le_roundMagTiesToEven {N : ℤ} {y : ℝ} (h : (N : ℝ) ≤ y) : N ≤ roundMagTiesToEven y := by
  have h1 := ceil_sub_half_le_roundMagTiesToEven y
  have : N ≤ ⌈y - 1 / 2⌉ := Int.le_ceil_iff.mpr (by linarith)
  omega

/-- Rounding to nearest is at most an integer above the value. -/
theorem roundMagTiesToEven_le {N : ℤ} {y : ℝ} (h : y ≤ N) : roundMagTiesToEven y ≤ N := by
  have h1 := roundMagTiesToEven_le_floor_add_half y
  have : ⌊y + 1 / 2⌋ < N + 1 := Int.floor_lt.mpr (by push_cast; linarith)
  omega

end SoftFloat.FloatLib.Proof
