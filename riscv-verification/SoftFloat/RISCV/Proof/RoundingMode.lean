/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.RISCV.Spec.Instructions
import SoftFloat.RISCV.Operators.Riscv

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.RISCV.Spec

theorem toRoundingDirection_constructors :
    RoundingMode.RNE.toRoundingDirection = .roundTiesToEven ∧
      RoundingMode.RTZ.toRoundingDirection = .roundTowardZero ∧
      RoundingMode.RDN.toRoundingDirection = .roundTowardNegative ∧
      RoundingMode.RUP.toRoundingDirection = .roundTowardPositive ∧
      RoundingMode.RMM.toRoundingDirection = .roundTiesToAway :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem decode_toRoundingDirection (rm frm : BitVec 3) :
    (riscv.decode rm frm).map RoundingMode.toRoundingDirection =
      selectedRoundingDirection rm.toNat frm.toNat := by
  have hsel : selectedRoundingDirection rm.toNat frm.toNat =
      roundingModeEncoding (if rm.toNat = 7 then frm else rm).toNat := by
    unfold selectedRoundingDirection
    split <;> rfl
  rw [hsel]
  have h := (if rm.toNat = 7 then frm else rm).isLt
  dsimp only [riscv]
  generalize (if rm.toNat = 7 then frm else rm).toNat = n at h ⊢
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

theorem toRoundingDirection_injective {m₁ m₂ : RoundingMode}
    (h : m₁.toRoundingDirection = m₂.toRoundingDirection) : m₁ = m₂ := by
  cases m₁ <;> cases m₂ <;> first | rfl | cases h

theorem decode_unique {d₁ d₂ : Option RoundingMode}
    (h : d₁.map RoundingMode.toRoundingDirection = d₂.map RoundingMode.toRoundingDirection) : d₁ = d₂ := by
  cases d₁ <;> cases d₂ <;> simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq] at h ⊢
  exact toRoundingDirection_injective h

end SoftFloat.RISCV.Proof
