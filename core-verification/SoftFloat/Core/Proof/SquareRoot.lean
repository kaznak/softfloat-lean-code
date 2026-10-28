/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Sticky

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem isqrtAux_spec (N : ℕ) :
    ∀ i r : ℕ, r * r ≤ N → N < (r + 2 ^ i) * (r + 2 ^ i) →
      isqrtAux N i r * isqrtAux N i r ≤ N ∧ N < (isqrtAux N i r + 1) * (isqrtAux N i r + 1) := by
  intro i
  induction i with
  | zero => intro r hlo hhi; simpa [isqrtAux] using ⟨hlo, hhi⟩
  | succ i ih =>
    intro r hlo hhi
    have hp : (2 : ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
    by_cases hc : (r + 2 ^ i) * (r + 2 ^ i) ≤ N
    · simp only [isqrtAux, hc, ↓reduceIte]
      exact ih _ hc (by rw [show r + 2 ^ i + 2 ^ i = r + 2 ^ (i + 1) by omega]; exact hhi)
    · simp only [isqrtAux, hc, ↓reduceIte]
      exact ih _ hlo (Nat.lt_of_not_le hc)

theorem lt_two_pow_isqrt_fuel (N : ℕ) :
    N < 2 ^ (Nat.log2 N / 2 + 1) * 2 ^ (Nat.log2 N / 2 + 1) := by
  rw [← pow_add]
  exact lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem isqrt_eq_sqrt (N : ℕ) : isqrt N = Nat.sqrt N := by
  have h := isqrtAux_spec N _ 0 (by simp) (by simpa using lt_two_pow_isqrt_fuel N)
  exact Nat.eq_sqrt.2 ⟨h.1, h.2⟩

theorem sqrt_bracket (m t : ℕ) (q : ℤ) (heven : (q - t) % 2 = 0) :
    ((isqrt (m <<< t) : ℕ) : ℝ) * 2 ^ ((q - t) / 2) ≤ Real.sqrt (m * 2 ^ q) ∧
      Real.sqrt (m * 2 ^ q) < (((isqrt (m <<< t) : ℕ) : ℝ) + 1) * 2 ^ ((q - t) / 2) ∧
      (isqrt (m <<< t) * isqrt (m <<< t) = m <<< t ↔
        Real.sqrt (m * 2 ^ q) = ((isqrt (m <<< t) : ℕ) : ℝ) * 2 ^ ((q - t) / 2)) := by
  set N := m <<< t
  set e := (q - t) / 2
  have hq : q = t + 2 * e := by omega
  have hN : ((N : ℕ) : ℝ) = m * 2 ^ (t : ℤ) := by
    simp only [N, Nat.shiftLeft_eq]; push_cast; rw [zpow_natCast]
  have hv : Real.sqrt (m * 2 ^ q) = Real.sqrt N * 2 ^ e := by
    rw [hN, hq, zpow_add₀ two_ne_zero, ← mul_assoc, Real.sqrt_mul (show (0 : ℝ) ≤ m * 2 ^ (t : ℤ) by positivity),
      show (2 : ℝ) ^ (2 * e) = (2 ^ e) ^ 2 by rw [← zpow_natCast, ← zpow_mul]; ring_nf,
      Real.sqrt_sq (by positivity)]
  have hp : (0 : ℝ) < 2 ^ e := by positivity
  rw [hv, isqrt_eq_sqrt]
  refine ⟨mul_le_mul_of_nonneg_right (Real.nat_sqrt_le_real_sqrt) hp.le,
    mul_lt_mul_of_pos_right Real.real_sqrt_lt_nat_sqrt_succ hp, ?_⟩
  rw [mul_left_inj' hp.ne']
  constructor
  · intro h
    have h' : (N : ℝ) = (Nat.sqrt N : ℝ) * Nat.sqrt N := by exact_mod_cast h.symm
    rw [h']; exact Real.sqrt_mul_self (Nat.cast_nonneg _)
  · intro h
    have h2 : ((Nat.sqrt N : ℕ) : ℝ) * (Nat.sqrt N : ℕ) = (N : ℝ) := by
      rw [← h, Real.mul_self_sqrt (by positivity)]
    exact_mod_cast h2

theorem squareRoot_finite_spec (sp : Specialization) (dst : Format) (rm : RoundingDirection)
    (x : ℝ) (zn : Bool) (m : ℕ) (q : ℤ) (hm : 0 < m) (hx : x = m * 2 ^ q) (t : ℕ)
    (heven : (q - t) % 2 = 0) (ht : 2 * (dst.sigBits + 2) ≤ t) :
    RoundedResultOf sp dst rm (Real.sqrt x) zn
      (dst.roundPack sp rm false
        (2 * isqrt (m <<< t) + (if isqrt (m <<< t) * isqrt (m <<< t) = m <<< t then 0 else 1))
        ((q - t) / 2 - 1)) := by
  obtain ⟨h1, h2, h3⟩ := sqrt_bracket m t q heven
  have hval : Real.sqrt x = (if false then -1 else 1) * Real.sqrt (m * 2 ^ q) := by
    rw [hx]; simp
  rw [hval]
  refine roundedResultOf_roundPack_sticky sp dst rm false _ _ _ _ zn h1 h2
    (by split_ifs <;> omega) ?_ ?_
  · rw [← h3]; split_ifs <;> simp_all
  · have hN : 2 ^ (2 * (dst.sigBits + 2)) ≤ m <<< t := by
      rw [Nat.shiftLeft_eq]
      calc 2 ^ (2 * (dst.sigBits + 2)) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
        _ ≤ m * 2 ^ t := Nat.le_mul_of_pos_left _ hm
    rw [isqrt_eq_sqrt]
    refine Nat.le_sqrt.2 (le_trans ?_ hN)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem squareRootSpecOf_squareRoot (sp : Specialization) (hsp : Specialization.Valid sp)
    (fa dst : Format) (rm : RoundingDirection) (a : ℕ) :
    SquareRootSpecOf sp fa dst rm a (Format.squareRoot sp fa dst rm a) := by
  have hnan : sp.propagateNaN .squareRoot dst [(fa, a)] < 2 ^ dst.width :=
    (hsp.propagateNaN _ _ _).2
  unfold SquareRootSpecOf Format.squareRoot
  dsimp only
  rw [isNaNU_unpack, isSNaNU_unpack, arithIsInf_eq, arithIsZero_eq]
  cases hna : isNaN fa a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [arithSign_eq fa hna]
    cases hza : isZeroU (fa.unpack a)
    · cases hs : (fa.unpack a).sign
      · cases hia : fa.isInfU (fa.unpack a)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hfa := isFinite_of_not_isNaN_not_isInfU fa hna hia
          have hv : valR fa a = (fa.sigOf (fa.unpack a) : ℝ) * 2 ^ fa.ulpExpOf (fa.unpack a) := by
            rw [valR_eq_sigOf fa hfa, hs]; simp
          have h := squareRoot_finite_spec sp dst rm (valR fa a) false _ _
            (sigOf_pos fa hza) hv
            (if (fa.ulpExpOf (fa.unpack a) - ((2 * (dst.sigBits + 2) : ℕ) : ℤ)) % 2 = 0
              then 2 * (dst.sigBits + 2) else 2 * (dst.sigBits + 2) + 1)
            (by split_ifs <;> push_cast at * <;> omega) (by split_ifs <;> omega)
          exact ⟨h.1, h⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨pack_expMax_lt _ _, classify_pack_infinity _ _, trivial⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hnan, trivial, trivial⟩
    · simp only [↓reduceIte]
      exact ⟨pack_zero_lt _ _, classify_pack_zero _ _, trivial⟩
  · simp only [↓reduceIte]
    exact ⟨hnan, trivial, trivial⟩

theorem softfloat_squareRoot_spec (sp : Specialization) (hsp : Specialization.Valid sp) :
    ∀ fa dst rm a, a < 2 ^ fa.width →
      SquareRootSpecOf sp fa dst rm a ((softfloat sp).squareRoot fa dst rm a) :=
  fun fa dst rm a _ => squareRootSpecOf_squareRoot sp hsp fa dst rm a

theorem squareRootSpecOf_unique {sp : Specialization} {r₁ r₂ : Nat × StatusFlags}
    {fa dst : Format} {rm : RoundingDirection} {a : Nat}
    (h₁ : SquareRootSpecOf sp fa dst rm a r₁) (h₂ : SquareRootSpecOf sp fa dst rm a r₂) :
    r₁ = r₂ := by
  unfold SquareRootSpecOf at h₁ h₂; dsimp only at h₁ h₂
  obtain ⟨hw₁, h₁⟩ := h₁
  obtain ⟨hw₂, h₂⟩ := h₂
  split_ifs at h₁ h₂ <;> uniq_close

end SoftFloat.Proof
