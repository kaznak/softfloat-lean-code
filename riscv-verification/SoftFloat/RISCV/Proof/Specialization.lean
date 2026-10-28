/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.Core.Proof.Payload
import SoftFloat.RISCV.Spec.Choices
import SoftFloat.RISCV.Operators.Specialization

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof

theorem classify_canonicalNaN (fmt : Format) : classify fmt fmt.canonicalNaN = .quietNaN :=
  classify_pack_quietNaN fmt false (quietBit_lt fmt) le_rfl

theorem canonicalNaN_lt (fmt : Format) : fmt.canonicalNaN < 2 ^ fmt.width :=
  pack_lt fmt false (expMax_lt fmt) (quietBit_lt fmt)

theorem isNaN_canonicalNaN (fmt : Format) : isNaN fmt fmt.canonicalNaN = true := by
  unfold isNaN; rw [classify_canonicalNaN]

theorem isSignalingNaN_canonicalNaN (fmt : Format) : isSignalingNaN fmt fmt.canonicalNaN = false := by
  unfold isSignalingNaN; rw [classify_canonicalNaN]; rfl

theorem riscv_intOutOfRange (src : Format) (rm : RoundingDirection) (exact signed : Bool) (w x : Nat) :
    Specialization.riscv.intOutOfRange src rm exact signed w x = Spec.riscvIntOutOfRange src signed w x := by
  have hp : (0 : Int) < 2 ^ w := by positivity
  have hpn : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  have hw1 : ∀ v : Int, 0 ≤ v → v < 2 ^ w → (v % 2 ^ w).toNat = v.toNat := fun v h0 h1 => by
    rw [Int.emod_eq_of_lt h0 h1]
  have hw2 : ∀ v : Int, -(2 ^ w) ≤ v → v < 0 → (v % 2 ^ w).toNat = (v + 2 ^ w).toNat := fun v h0 h1 => by
    rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
  unfold Specialization.riscv Spec.riscvIntOutOfRange intRangeHi intRangeLo
  dsimp only
  rw [isNaNU_unpack]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · cases signed <;> cases isNaN src x <;> cases (src.unpack x).sign <;> simp
  · have h2 : (2 : Int) ^ w = 2 ^ (w - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have h2n : 2 ^ w = 2 ^ (w - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have hq : (0 : Int) < 2 ^ (w - 1) := by positivity
    have hqn : ((2 ^ (w - 1) : Nat) : Int) = 2 ^ (w - 1) := by push_cast; rfl
    cases signed <;> cases isNaN src x <;> cases (src.unpack x).sign <;> simp only [Bool.not_true,
      Bool.not_false, Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.true_eq_false, or_true, or_false,
      ↓reduceIte]
    all_goals first
      | (rw [hw1 _ (by omega) (by omega)]; omega)
      | (rw [hw2 _ (by omega) (by omega)]; omega)

theorem riscv_choices : Spec.RiscvChoices Specialization.riscv where
  propagateNaN _ _ _ := rfl
  bf16CanonicalNaN _ _ := (by decide : Format.bf16.canonicalNaN = 0x7FC0)
  fusedMultiplyAddZeroInfinityQuietNaNInvalid := rfl
  tininess := rfl
  intOutOfRange := riscv_intOutOfRange

theorem riscv_valid : Spec.Specialization.Valid Specialization.riscv where
  propagateNaN op dst xs := ⟨classify_canonicalNaN dst, canonicalNaN_lt dst⟩
  intOutOfRange src rm exact signed w x := by
    rw [riscv_intOutOfRange]
    exact toNat_emod_two_pow_lt _ w
  totalOrderNaN fmt c s hc := by
    have hle : ∀ x y, Specialization.riscv.totalOrderNaN fmt x y =
        if (fmt.unpack x).sign then decide (nanPayload fmt y ≤ nanPayload fmt x)
        else decide (nanPayload fmt x ≤ nanPayload fmt y) := fun _ _ => rfl
    refine ⟨fun x y hx hy => ?_, fun x y hx hy h₁ h₂ => ?_, fun x y z hx hy hz h₁ h₂ => ?_⟩
    · simp only [hle, hx.2.2, hy.2.2]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] <;> omega
    · simp only [hle, hx.2.2, hy.2.2] at h₁ h₂
      have hp : nanPayload fmt x = nanPayload fmt y := by
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h₁ h₂ <;> omega
      have hna : isNaN fmt x = true := by
        unfold isNaN; rw [hx.2.1]; rcases hc with rfl | rfl <;> rfl
      exact eq_of_nanPayload_eq hx.1 hy.1 hna (hx.2.1.trans hy.2.1.symm) (hx.2.2.trans hy.2.2.symm) hp
    · simp only [hle, hx.2.2, hy.2.2] at h₁ h₂ ⊢
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h₁ h₂ ⊢ <;> omega
  admissiblePayload signaling fmt n h := by
    have hq : fmt.quietBit = 2 ^ (fmt.fracBits - 1) := rfl
    simp only [Specialization.riscv, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at h
    refine ⟨hq ▸ h.1, fun hs => ?_⟩
    rcases h.2 with h' | h'
    · rw [hs] at h'; cases h'
    · exact h'
  minNumMaxNumOfEqual eq fmt x y := by
    cases eq <;> simp only [Specialization.riscv] <;> split <;> simp
  minNumMagOfEqual _ _ _ := ⟨rfl, rfl⟩
  minNumMagNaN _ _ := ⟨rfl, rfl⟩
  scaleBOfNaNExponent fmt rm x n := canonicalNaN_lt fmt

end SoftFloat.RISCV.Proof
