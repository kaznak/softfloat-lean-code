/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Common

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem roundIncr_quot_ne_iff (rm : RoundingDirection) (neg : Bool) (m d : ℕ) (hd : 0 < d) :
    m % d ≠ 0 ↔
      (((if roundIncr rm neg (m / d) (m % d) d then m / d + 1 else m / d : ℕ) : ℝ) ≠ (m : ℝ) / d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro hr heq
    have h := roundIncr_eq_roundAbs rm neg m d hd
    have hm : (m : ℝ) = ((if roundIncr rm neg (m / d) (m % d) d then m / d + 1 else m / d : ℕ) : ℝ)
        * d := by
      rw [heq]; field_simp
    have hm' : m = (if roundIncr rm neg (m / d) (m % d) d then m / d + 1 else m / d) * d := by
      exact_mod_cast hm
    apply hr; rw [hm']; exact Nat.mul_mod_left _ _
  · intro hne hr
    apply hne
    have hinc : roundIncr rm neg (m / d) (m % d) d = false := by
      cases rm <;> simp [roundIncr, hr] <;> omega
    rw [hinc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hm : m = m / d * d := by
      have := Nat.div_add_mod m d; rw [hr] at this; linarith
    rw [eq_div_iff hdR.ne']
    exact_mod_cast hm.symm

theorem natCast_mul_zpow_neg (m : ℕ) {q : ℤ} (hq : q < 0) :
    (m : ℝ) * (2 : ℝ) ^ q = (m : ℝ) / ((2 ^ (-q).toNat : ℕ) : ℝ) := by
  have h : q = -(((-q).toNat : ℕ) : ℤ) := by omega
  conv_lhs => rw [h, zpow_neg, zpow_natCast]
  push_cast; ring

theorem natCast_mul_zpow_nonneg (m : ℕ) {q : ℤ} (hq : 0 ≤ q) :
    (m : ℝ) * (2 : ℝ) ^ q = ((m <<< q.toNat : ℕ) : ℝ) := by
  have h : q = ((q.toNat : ℕ) : ℤ) := by omega
  rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← h]

theorem intResult_spec (inv : ℕ) (rm : RoundingDirection) (s exact signed : Bool)
    (w : ℕ) (x y : ℝ) (z : ℕ) (ix : Bool)
    (hx : x = (if s then -1 else 1) * y) (hy : 0 ≤ y) (hz : roundAbs rm s y = z)
    (hix : ix = true ↔ (z : ℝ) ≠ y) :
    let n := integralPartOf rm s x
    let r : ℕ × StatusFlags :=
      let v : ℤ := if s then -(z : ℤ) else (z : ℤ)
      let lo : ℤ := if signed then -(2 ^ (w - 1) : ℤ) else 0
      let hi : ℤ := if signed then (2 ^ (w - 1) : ℤ) - 1 else (2 ^ w : ℤ) - 1
      if v < lo then (inv, { invalidOperation := true })
      else if hi < v then (inv, { invalidOperation := true })
      else ((if s then (2 ^ w - z) % 2 ^ w else z), { inexact := exact && ix })
    if n < intRangeLo signed w then r = (inv, { invalidOperation := true })
    else if intRangeHi signed w < n then r = (inv, { invalidOperation := true })
    else r.1 = (n % (2 ^ w : ℤ)).toNat ∧ integralFlagsOf exact ((n : ℝ) ≠ x) r.2 := by
  intro n r
  have habs : |x| = y := by
    rw [hx]; cases s <;> simp [abs_of_nonneg hy]
  have hn : n = if s then -(z : ℤ) else (z : ℤ) := by
    simp only [n, integralPartOf, habs, hz]; cases s <;> simp
  have hch : ((n : ℝ) ≠ x) ↔ (z : ℝ) ≠ y := by
    rw [hn, hx]; cases s <;> simp
  have hlo : intRangeLo signed w = if signed then -(2 ^ (w - 1) : ℤ) else 0 := rfl
  have hhi : intRangeHi signed w = if signed then (2 ^ (w - 1) : ℤ) - 1 else (2 ^ w : ℤ) - 1 := rfl
  have hpw : (2 : ℤ) ^ (w - 1) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  by_cases h1 : n < intRangeLo signed w
  · simp only [h1, ↓reduceIte, r, ← hn, ← hlo]
  by_cases h2 : intRangeHi signed w < n
  · simp only [h1, h2, ↓reduceIte, r, ← hn, ← hlo, ← hhi]
  simp only [h1, h2, ↓reduceIte, r, ← hn, ← hlo, ← hhi]
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · rw [hn]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢
      have hz' : (z : ℤ) < 2 ^ w := by
        rw [hn, hhi] at h2; split_ifs at h2 <;> omega
      rw [Int.emod_eq_of_lt (by omega) hz']; simp
    · simp only [↓reduceIte] at hn ⊢
      have hz' : (z : ℤ) ≤ 2 ^ w := by
        rw [hn, hlo] at h1; split_ifs at h1 <;> omega
      have hzN : z ≤ 2 ^ w := by exact_mod_cast hz'
      have hm : (((2 ^ w - z) % 2 ^ w : ℕ) : ℤ) = -(z : ℤ) % 2 ^ w := by
        rw [Int.natCast_mod, Nat.cast_sub hzN]; push_cast
        rw [show (2 : ℤ) ^ w - z = -z + 2 ^ w by ring]; simp
      rw [← hm, Int.toNat_natCast]
  · simp only [Bool.and_eq_true, hch, ← hix]

theorem convertToInteger_spec_of_isFinite (sp : Specialization) (fmt : Format)
    (rm : RoundingDirection) (exact signed : Bool) (w a : ℕ) (hf : IsFinite fmt a) :
    let inv := sp.intOutOfRange fmt rm exact signed w a
    let s := (fmt.unpack a).sign
    let n := integralPartOf rm s (valR fmt a)
    let r := fmt.convertToInteger sp rm exact signed w a
    if n < intRangeLo signed w then r = (inv, { invalidOperation := true })
    else if intRangeHi signed w < n then r = (inv, { invalidOperation := true })
    else r.1 = (n % (2 ^ w : ℤ)).toNat ∧ integralFlagsOf exact ((n : ℝ) ≠ valR fmt a) r.2 := by
  intro inv s n r
  have hN := isNaNU_eq_false_of_isFinite fmt hf
  have hI := isInfU_eq_false_of_isFinite fmt hf
  have hv := valR_eq_sigOf fmt hf
  simp only [r, Format.convertToInteger, hN, hI, Bool.false_eq_true, ↓reduceIte]
  by_cases hq : 0 ≤ fmt.ulpExpOf (fmt.unpack a)
  · simp only [hq, ↓reduceIte]
    exact intResult_spec inv rm s exact signed w (valR fmt a)
      ((fmt.sigOf (fmt.unpack a) : ℝ) * (2 : ℝ) ^ fmt.ulpExpOf (fmt.unpack a))
      (fmt.sigOf (fmt.unpack a) <<< (fmt.ulpExpOf (fmt.unpack a)).toNat) false
      (by rw [hv]; ring) (by positivity)
      (by rw [natCast_mul_zpow_nonneg _ hq, roundAbs_natCast])
      (by simp [natCast_mul_zpow_nonneg _ hq])
  · simp only [hq, ↓reduceIte]
    have hq' : fmt.ulpExpOf (fmt.unpack a) < 0 := lt_of_not_ge hq
    have hd : 0 < 2 ^ (-fmt.ulpExpOf (fmt.unpack a)).toNat := Nat.two_pow_pos _
    exact intResult_spec inv rm s exact signed w (valR fmt a)
      ((fmt.sigOf (fmt.unpack a) : ℝ) / ((2 ^ (-fmt.ulpExpOf (fmt.unpack a)).toNat : ℕ) : ℝ))
      _ _
      (by rw [hv, ← natCast_mul_zpow_neg _ hq']; ring) (by positivity)
      (roundIncr_eq_roundAbs rm s _ _ hd).symm
      (by rw [bne_iff_ne]; exact roundIncr_quot_ne_iff rm s _ _ hd)

theorem softfloat_convertToInteger_spec (sp : Specialization) :
    ∀ fmt rm exact signed w a, 0 < w → a < 2 ^ fmt.width →
      ConvertToIntegerSpecOf sp fmt rm exact signed w a
        ((softfloat sp).convertToInteger fmt rm exact signed w a) := by
  intro fmt rm exact signed w a _ _
  show ConvertToIntegerSpecOf sp fmt rm exact signed w a
    (fmt.convertToInteger sp rm exact signed w a)
  have hfin := convertToInteger_spec_of_isFinite sp fmt rm exact signed w a
  have hnan := isNaNU_unpack fmt a
  unfold ConvertToIntegerSpecOf
  cases hc : classify fmt a with
  | quietNaN =>
    have h : isNaN fmt a = true := by simp [isNaN, hc]
    simp [Format.convertToInteger, hnan, h]
  | signalingNaN =>
    have h : isNaN fmt a = true := by simp [isNaN, hc]
    simp [Format.convertToInteger, hnan, h]
  | infinity t =>
    have hi := ((classify_eq_infinity_iff fmt a t).1 hc).1
    have h : isNaN fmt a = false := by simp [isNaN, hc]
    simp [Format.convertToInteger, hnan, h, hi]
  | normal t =>
    obtain ⟨_, hs⟩ := (classify_eq_normal_iff fmt a t).1 hc
    subst hs; exact hfin (by simp [IsFinite, hc])
  | subnormal t =>
    obtain ⟨_, hs⟩ := (classify_eq_subnormal_iff fmt a t).1 hc
    subst hs; exact hfin (by simp [IsFinite, hc])
  | zero t =>
    obtain ⟨_, hs⟩ := (classify_eq_zero_iff fmt a t).1 hc
    subst hs; exact hfin (by simp [IsFinite, hc])

theorem integralFlagsOf_unique {exact : Bool} {changed : Prop} {f g : StatusFlags}
    (hf : integralFlagsOf exact changed f) (hg : integralFlagsOf exact changed g) : f = g :=
  statusFlags_eq (bool_eq_of_iff hf.1 hg.1) (hf.2.1.trans hg.2.1.symm)
    (hf.2.2.1.trans hg.2.2.1.symm) (hf.2.2.2.1.trans hg.2.2.2.1.symm)
    (hf.2.2.2.2.trans hg.2.2.2.2.symm)

theorem convertToIntegerSpecOf_unique {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}
    {fmt : Format} {rm : RoundingDirection} {exact signed : Bool} {w a : Nat}
    (h₁ : ConvertToIntegerSpecOf sp fmt rm exact signed w a r₁)
    (h₂ : ConvertToIntegerSpecOf sp fmt rm exact signed w a r₂) : r₁ = r₂ := by
  unfold ConvertToIntegerSpecOf at h₁ h₂
  cases hc : classify fmt a <;> simp only [hc] at h₁ h₂
  all_goals first
    | exact h₁.trans h₂.symm
    | (split_ifs at h₁ h₂
       · exact h₁.trans h₂.symm
       · exact h₁.trans h₂.symm
       · exact Prod.ext (h₁.1.trans h₂.1.symm) (integralFlagsOf_unique h₁.2 h₂.2))

end SoftFloat.Proof
