/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Proof.Round
import FloatLib.Floats.Formats.BinaryInterchange.Status.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness

/-!
# The dyadic rounding of FloatLib

The sign, the finiteness and the boundaries of `Model.roundDyadic`, the rounding of an exact
dyadic to nearest with ties to even, in the format `toFL fmt`.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec
open _root_.FloatLib.Floats.Formats.BinaryInterchange (FloatFormat Model)

local notation "Dyadic" => _root_.FloatLib.Numerics.Dyadic

variable {fmt : Format}

/-! ## The real value of a dyadic -/

theorem abs_toReal_dyadic (d : Dyadic) : |d.toReal| = (d.significand : ℝ) * 2 ^ d.exponent := by
  rw [Model.Dyadic.abs_toReal, bpow_binary]

theorem toReal_nonneg_dyadic (d : Dyadic) :
    ({ d with negative := false } : Dyadic).toReal = |d.toReal| := by
  rw [abs_toReal_dyadic]
  simp [_root_.FloatLib.Numerics.Dyadic.toReal, _root_.FloatLib.Numerics.Dyadic.signedSignificand]

theorem toReal_neg_iff (d : Dyadic) (h : d.significand ≠ 0) : d.toReal < 0 ↔ d.negative = true := by
  have hm : (0 : ℝ) < d.significand := by exact_mod_cast Nat.pos_of_ne_zero h
  have hp : (0 : ℝ) < (2 : ℝ) ^ d.exponent := by positivity
  simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
    _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand]
  cases d.negative
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, iff_false, not_lt]; positivity
  · simp only [↓reduceIte, neg_mul, one_mul, neg_lt_zero, iff_true]; positivity

theorem toReal_eq_zero_iff (d : Dyadic) : d.toReal = 0 ↔ d.significand = 0 := by
  rw [← abs_eq_zero, abs_toReal_dyadic]
  have hp : (2 : ℝ) ^ d.exponent ≠ 0 := by positivity
  simp [hp]

/-! ## The boundaries of FloatLib -/

theorem maxFiniteFracField_toFL (fmt : Format) :
    (toFL fmt).maxFiniteFracField = 2 ^ fmt.fracBits - 1 := rfl

theorem toReal_overflowMidpoint (fmt : Format) :
    (Model.overflowMidpoint (toFL fmt)).toReal = midR fmt := by
  have hs := sigBits_eq_fracBits_add_one fmt
  have h1 : 1 ≤ 2 ^ fmt.fracBits := Nat.one_le_two_pow
  unfold Model.overflowMidpoint Model.maxFiniteDyadic midR
  simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
    _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand, Bool.false_eq_true, ↓reduceIte,
    one_mul, maxFiniteFracField_toFL, maxNormalExponent_toFL, fracWidth_toFL, Model.pow2_eq_two_pow,
    Int.ofNat_eq_natCast]
  rw [show emax fmt + 1 - (fmt.sigBits : ℤ) = ((fmt.bias : ℤ) - fmt.fracBits - 1) + 1 by
    unfold emax; push_cast [hs]; ring, zpow_add_one₀ two_ne_zero, hs]
  push_cast [h1]
  rw [pow_succ]
  ring

theorem toReal_underflowMidpoint (fmt : Format) :
    (Model.underflowMidpoint (toFL fmt)).toReal = umidR fmt := by
  have hs := sigBits_eq_fracBits_add_one fmt
  have h1 : 1 ≤ 4 * 2 ^ fmt.fracBits := by have := Nat.one_le_two_pow (n := fmt.fracBits); omega
  unfold Model.underflowMidpoint umidR
  simp only [_root_.FloatLib.Numerics.Dyadic.toReal,
    _root_.FloatLib.Numerics.Dyadic.cast_signedSignificand, Bool.false_eq_true, ↓reduceIte,
    one_mul, fracWidth_toFL, Model.pow2_eq_two_pow, minSubnormalExponent_toFL]
  rw [show emin fmt - (fmt.sigBits : ℤ) = (fmt.minQ - 2) + 1 by
    unfold emin emax Format.minQ; push_cast [hs]; ring, zpow_add_one₀ two_ne_zero, hs]
  push_cast [h1]
  rw [pow_succ]
  ring

theorem maxFiniteMantissaOdd_toFL (fmt : Format) : Model.maxFiniteMantissaOdd (toFL fmt) = true := by
  have h1 : 1 ≤ 2 ^ fmt.fracBits := Nat.one_le_two_pow
  unfold Model.maxFiniteMantissaOdd Model.maxFiniteDyadic
  simp only [maxFiniteFracField_toFL, fracWidth_toFL, Model.pow2_eq_two_pow, beq_iff_eq]
  omega

/-- FloatLib signals overflow exactly when the exact value is at least `midR`. -/
theorem nearestEvenOverflows_iff (d : Dyadic) :
    Model.dyadicNearestEvenOverflows (toFL fmt) d = true ↔ midR fmt ≤ |d.toReal| := by
  unfold Model.dyadicNearestEvenOverflows
  have hlt := Model.cmpDyadic_lt_iff { d with negative := false } (Model.overflowMidpoint (toFL fmt))
  have heq := Model.cmpDyadic_eq_iff { d with negative := false } (Model.overflowMidpoint (toFL fmt))
  have hgt := Model.cmpDyadic_gt_iff { d with negative := false } (Model.overflowMidpoint (toFL fmt))
  rw [toReal_nonneg_dyadic, toReal_overflowMidpoint] at hlt heq hgt
  split
  · rename_i h; rw [hgt] at h; simp only [true_iff]; exact h.le
  · rename_i h; rw [heq] at h; rw [maxFiniteMantissaOdd_toFL]; simp only [true_iff]; exact h.ge
  · rename_i h; rw [hlt] at h; simp only [Bool.false_eq_true, false_iff, not_le]; exact h

/-- FloatLib compares the exact value with `umidR` for tininess. -/
theorem lt_underflowMidpoint_iff (d : Dyadic) :
    ({ d with negative := false } : Dyadic).toReal < (Model.underflowMidpoint (toFL fmt)).toReal ↔
      |d.toReal| < umidR fmt := by
  rw [toReal_nonneg_dyadic, toReal_underflowMidpoint]


/-! ## The rounding kernel -/

theorem roundDyadic_eq_kernel (d : Dyadic) :
    Model.roundDyadic (toFL fmt) d = Model.Internal.ieeeRoundDyadic (toFL fmt) d := by
  rw [Model.roundDyadic_eq_internal]
  unfold Model.Internal.roundDyadic
  simp only [isIEEE_toFL, ↓reduceIte]

theorem expAllOnesNat_toFL_eq (fmt : Format) :
    FloatFormat.expAllOnesNat (toFL fmt) = 2 * fmt.bias + 1 := by
  rw [expAllOnesNat_toFL, expMax_eq_two_mul_bias_add_one]

theorem isFinite_ofFields_toFL (s : Bool) {e : Nat} (f : Nat) (he : e ≤ 2 * fmt.bias) :
    Model.isFinite (Model.ofFields (toFL fmt) s e f) = true :=
  Model.isFinite_ofFields_ieee _ (isIEEE_toFL fmt) s e f (by rw [expAllOnesNat_toFL_eq]; omega)

theorem isFinite_signedZero_toFL (s : Bool) :
    Model.isFinite (if s then Model.negZero (toFL fmt) else Model.posZero (toFL fmt)) = true := by
  cases s
  · exact Model.isFinite_posZero _
  · exact Model.isFinite_negZero _ (FloatFormat.supportsSignedZero_eq_true_of_isIEEE _ (isIEEE_toFL fmt))

theorem signBit_signedZero_toFL (s : Bool) :
    Model.signBit (if s then Model.negZero (toFL fmt) else Model.posZero (toFL fmt)) = s := by
  cases s <;> simp

theorem signBit_signedInf_toFL (s : Bool) :
    Model.signBit (if s then Model.negInf (toFL fmt) else Model.posInf (toFL fmt)) = s := by
  cases s <;> simp

theorem isInf_signedInf_toFL (s : Bool) :
    Model.isInf (if s then Model.negInf (toFL fmt) else Model.posInf (toFL fmt)) = true := by
  have h := FloatFormat.supportsInfinity_eq_true_of_isIEEE _ (isIEEE_toFL fmt)
  cases s
  · exact Model.isInf_posInf _ h
  · exact Model.isInf_negInf _ h

theorem encodedExponent_le (k : Int) (h1 : 1 - (fmt.bias : Int) ≤ k) (h2 : k ≤ fmt.bias) :
    Int.toNat (k + Int.ofNat (toFL fmt).bias) ≤ 2 * fmt.bias := by
  rw [bias_toFL]
  simp only [Int.ofNat_eq_natCast]
  omega

theorem signBit_roundDyadic (d : Dyadic) :
    Model.signBit (Model.roundDyadic (toFL fmt) d) = d.negative := by
  rw [roundDyadic_eq_kernel]
  unfold Model.Internal.ieeeRoundDyadic
  simp only [apply_ite (Model.signBit (fmt := toFL fmt)), Model.signBit_ofFields,
    Model.signBit_negZero, Model.signBit_posZero, Model.signBit_negInf, Model.signBit_posInf,
    ite_self]
  cases d.negative <;> simp

theorem isFinite_or_isInf_roundDyadic (d : Dyadic) :
    Model.isFinite (Model.roundDyadic (toFL fmt) d) = true ∨
      Model.isInf (Model.roundDyadic (toFL fmt) d) = true := by
  have hinf := FloatFormat.supportsInfinity_eq_true_of_isIEEE _ (isIEEE_toFL fmt)
  have hsz := FloatFormat.supportsSignedZero_eq_true_of_isIEEE _ (isIEEE_toFL fmt)
  have hb := one_le_bias fmt
  rw [roundDyadic_eq_kernel]
  unfold Model.Internal.ieeeRoundDyadic
  simp only [beq_iff_eq]
  split_ifs
  all_goals first
    | exact Or.inr (Model.isInf_negInf _ hinf)
    | exact Or.inr (Model.isInf_posInf _ hinf)
    | exact Or.inl (Model.isFinite_posZero _)
    | exact Or.inl (Model.isFinite_negZero _ hsz)
    | exact Or.inl (isFinite_ofFields_toFL _ _ (by omega))
    | refine Or.inl (isFinite_ofFields_toFL _ _ (encodedExponent_le _ ?_ ?_)) <;>
      simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.ieeeMaxNormalExponent, bias_toFL,
        Int.ofNat_eq_natCast, gt_iff_lt, not_lt] at * <;> omega


/-- The top exponent of a dyadic below `2 ^ (emax + 1)` is at most `emax`. -/
theorem topExp_le_of_lt (d : Dyadic) (h0 : d.significand ≠ 0)
    (h : |d.toReal| < 2 ^ (emax fmt + 1)) :
    (d.significand.log2 : Int) + d.exponent ≤ fmt.bias := by
  have hle : (2 : ℝ) ^ ((d.significand.log2 : Int) + d.exponent) ≤ |d.toReal| := by
    rw [abs_toReal_dyadic, zpow_add₀ two_ne_zero, zpow_natCast]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.log2_self_le h0
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hle.trans_lt h)
  unfold emax at this
  omega

/-- At the top exponent `emax`, a dyadic below `midR` is rounded to fewer than `2 ^ sigBits`
units. -/
theorem roundShiftRightEven_lt_of_lt (d : Dyadic) (hf : fmt.fracBits ≤ d.significand.log2)
    (hk : (d.significand.log2 : Int) + d.exponent = fmt.bias) (h : |d.toReal| < midR fmt) :
    _root_.FloatLib.Numerics.roundShiftRightEven d.significand (d.significand.log2 - fmt.fracBits) <
      2 ^ (fmt.fracBits + 1) := by
  have hs := sigBits_eq_fracBits_add_one fmt
  have key := Model.nearestEven_div_pow2_eq_roundShiftRightEven d.significand
    (d.significand.log2 - fmt.fracBits)
  rw [nearestEven_eq, Model.pow2_eq_two_pow] at key
  have hc : ((d.significand.log2 - fmt.fracBits : ℕ) : ℤ) = emax fmt + 1 - fmt.sigBits - d.exponent := by
    unfold emax; push_cast [hf, hs]; omega
  have hy : (d.significand : ℝ) / ((2 ^ (d.significand.log2 - fmt.fracBits) : ℕ) : ℝ) =
      |d.toReal| / 2 ^ (emax fmt + 1 - fmt.sigBits) := by
    rw [abs_toReal_dyadic, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, hc,
      zpow_sub₀ two_ne_zero]
    field_simp
  rw [hy] at key
  have hlt : roundMagTiesToEven (|d.toReal| / 2 ^ (emax fmt + 1 - fmt.sigBits)) < 2 ^ fmt.sigBits := by
    rw [roundMagTiesToEven_lt_iff (two_pow_sigBits_even fmt), div_lt_iff₀ (by positivity)]
    unfold midR at h
    push_cast
    exact h
  rw [key, Int.ofNat_eq_natCast] at hlt
  rw [← hs]
  exact_mod_cast hlt

/-- A dyadic below `midR` rounds to a finite value. -/
theorem isFinite_roundDyadic_of_lt (d : Dyadic) (h : |d.toReal| < midR fmt) :
    Model.isFinite (Model.roundDyadic (toFL fmt) d) = true := by
  have hinf := FloatFormat.supportsInfinity_eq_true_of_isIEEE _ (isIEEE_toFL fmt)
  have hsz := FloatFormat.supportsSignedZero_eq_true_of_isIEEE _ (isIEEE_toFL fmt)
  have hb := one_le_bias fmt
  have hmid : midR fmt ≤ 2 ^ (emax fmt + 1) := by
    have e : (2 : ℝ) ^ (emax fmt + 1) = 2 ^ fmt.sigBits * 2 ^ (emax fmt + 1 - fmt.sigBits) := by
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]; ring_nf
    unfold midR
    rw [e]
    have : (0 : ℝ) < 2 ^ (emax fmt + 1 - fmt.sigBits) := by positivity
    nlinarith
  by_cases h0 : d.significand = 0
  · rw [roundDyadic_eq_kernel]
    unfold Model.Internal.ieeeRoundDyadic
    simp only [h0, beq_self_eq_true, ↓reduceIte]
    exact isFinite_signedZero_toFL _
  have hk := topExp_le_of_lt d h0 (h.trans_le hmid)
  have hc1 : fmt.fracBits ≤ d.significand.log2 → (d.significand.log2 : Int) + d.exponent = fmt.bias →
      _root_.FloatLib.Numerics.roundShiftRightEven d.significand (d.significand.log2 - fmt.fracBits) <
        2 ^ (fmt.fracBits + 1) := fun hf hk => roundShiftRightEven_lt_of_lt d hf hk h
  have hc2 : ¬ fmt.fracBits ≤ d.significand.log2 →
      d.significand <<< (fmt.fracBits - d.significand.log2) < 2 ^ (fmt.fracBits + 1) := by
    intro hf
    rw [Nat.shiftLeft_eq]
    have h1 : d.significand < 2 ^ (d.significand.log2 + 1) := Nat.lt_log2_self
    calc d.significand * 2 ^ (fmt.fracBits - d.significand.log2)
        < 2 ^ (d.significand.log2 + 1) * 2 ^ (fmt.fracBits - d.significand.log2) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ (fmt.fracBits + 1) := by rw [← pow_add]; congr 1; omega
  rw [roundDyadic_eq_kernel]
  unfold Model.Internal.ieeeRoundDyadic
  simp only [beq_iff_eq]
  split_ifs
  all_goals first
    | with_reducible exact Model.isFinite_posZero _
    | with_reducible exact Model.isFinite_negZero _ hsz
    | with_reducible exact isFinite_ofFields_toFL _ 0 (by omega)
    | (with_reducible refine isFinite_ofFields_toFL _ _ (encodedExponent_le _ ?_ ?_)) <;>
      simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.ieeeMaxNormalExponent, bias_toFL,
        Int.ofNat_eq_natCast, gt_iff_lt, not_lt] at * <;> omega
    | with_reducible exact isFinite_ofFields_toFL _ _ (by omega)
    | (exfalso
       simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.ieeeMaxNormalExponent, bias_toFL,
         Int.ofNat_eq_natCast, gt_iff_lt, not_lt, fracWidth_toFL, Model.pow2_eq_two_pow] at *
       omega)

end SoftFloat.FloatLib.Proof
