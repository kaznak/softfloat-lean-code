/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Proof.RoundPack
import SoftFloat.Core.Proof.RoundR
import SoftFloat.Core.Proof.RoundToIntegral
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.RISCV.Spec.Zfa

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem abs_valR_le_maxFinite (fmt : Format) {n : Nat} (hf : IsFinite fmt n) :
    |valR fmt n| ≤ maxFinite fmt := by
  have hv := valR_eq_sigOf fmt hf
  have hm := sigOf_lt_two_pow_sigBits fmt (fmt.unpack n) (unpack_fracField_lt fmt n)
  have hE := expField_lt_expMax_of_isFinite fmt hf
  have he := expMax_eq_two_mul_bias_add_one fmt
  have hb := one_le_bias fmt
  have hV : fmt.ulpExpOf (fmt.unpack n) + fmt.fracBits ≤ emax fmt := by
    unfold Format.ulpExpOf emax
    split_ifs <;> omega
  have hle := mul_two_zpow_le_maxFinite fmt hm hV
  rw [hv, abs_mul, abs_mul]
  have h1 : |(if (fmt.unpack n).sign then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> simp
  rw [h1, one_mul, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
  exact hle

theorem maxFinite_lt_two_zpow (fmt : Format) : maxFinite fmt < 2 ^ (emax fmt + 1) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  unfold maxFinite
  have : (0 : ℝ) < 2 ^ (1 - (fmt.sigBits : ℤ)) := by positivity
  rw [zpow_add_one₀ h2]
  have : (0 : ℝ) < 2 ^ emax fmt := by positivity
  nlinarith

theorem abs_valR_lt (fmt : Format) {n : Nat} (hf : IsFinite fmt n) :
    |valR fmt n| < 2 ^ (emax fmt + 1) :=
  lt_of_le_of_lt (abs_valR_le_maxFinite fmt hf) (maxFinite_lt_two_zpow fmt)

theorem integralPartOf_roundTowardZero_bounds (s : Bool) {x : ℝ} {B : ℕ} (hx : |x| < B) :
    -(B : ℤ) < integralPartOf .roundTowardZero s x ∧ integralPartOf .roundTowardZero s x < B := by
  unfold integralPartOf roundAbs roundMagDown
  have h0 : (0 : ℤ) ≤ ⌊|x|⌋ := Int.floor_nonneg.2 (abs_nonneg x)
  have h1 : ⌊|x|⌋ < (B : ℤ) := by
    rw [Int.floor_lt]; exact_mod_cast hx
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem valR_eq_of_fields {fmt : Format} {n : Nat} (hf : IsFinite fmt n) {s : Bool} {m : Nat} {e : Int}
    (hs : (fmt.unpack n).sign = s) (hm : fmt.sigOf (fmt.unpack n) = m) (he : fmt.ulpExpOf (fmt.unpack n) = e) :
    valR fmt n = (if s then -1 else 1) * (m : ℝ) * 2 ^ e := by
  rw [valR_eq_sigOf fmt hf, hs, hm, he]

theorem valR_of_fields {fmt : Format} {n : Nat} {x : ℝ} (hf : IsFinite fmt n) {s : Bool} {m : Nat} {e : Int}
    (hs : (fmt.unpack n).sign = s) (hm : fmt.sigOf (fmt.unpack n) = m) (he : fmt.ulpExpOf (fmt.unpack n) = e)
    (hx : (if s then -1 else 1) * (m : ℝ) * 2 ^ e = x) : valR fmt n = x := by
  rw [valR_eq_of_fields hf hs hm he, hx]

theorem bitVec5_cases {P : BitVec 5 → Prop} (h : ∀ k, k < 32 → P (BitVec.ofNat 5 k)) : ∀ i, P i := by
  intro i
  have := h i.toNat i.isLt
  simpa using this

theorem two_pow_mul_two_zpow (j : ℕ) (e k : ℤ) (h : (j : ℤ) + e = k) :
    (if false = true then (-1 : ℝ) else 1) * ((2 ^ j : ℕ) : ℝ) * 2 ^ e = 2 ^ k := by
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ two_ne_zero, h]

theorem loadImmediate_value {fmt : Format} {x : ℝ} {r : Nat} (he : fmt.IsEncoding r) (hf : IsFinite fmt r)
    (hv : valR fmt r = x) : LoadImmediateValueOf fmt (.value x) r :=
  ⟨fun _ => ⟨hf, hv⟩, fun hn => (hn ⟨r, he, hf, hv⟩).elim⟩

theorem loadImmediate_overflow {fmt : Format} {x : ℝ} {r : Nat} (hx : maxFinite fmt < x)
    (hr : classify fmt r = .infinity false) : LoadImmediateValueOf fmt (.value x) r := by
  refine ⟨fun ⟨n, _, hf, hv⟩ => ?_, fun _ => hr⟩
  have := abs_valR_le_maxFinite fmt hf
  rw [hv] at this
  exact absurd (lt_of_lt_of_le hx (le_trans (le_abs_self x) this)) (lt_irrefl _)

end SoftFloat.RISCV.Proof
