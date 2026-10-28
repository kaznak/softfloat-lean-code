/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.RISCV.Base
import SoftFloat.RISCV.Spec.Choices
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Spec.Agree
import SoftFloat.RISCV.Spec.Coverage
import SoftFloat.RISCV.Operators
import SoftFloat.RISCV.Proof.Riscv

namespace SoftFloat.RISCV.Claim

open SoftFloat

-- ANCHOR: RiscvClaim
theorem correctness : Spec.RiscvChoices Specialization.riscv ∧ Spec.RiscvCorrect Specialization.riscv riscv :=
  Proof.riscv_choices_correct

theorem uniqueness :
    ∀ sp₁ sp₂ o₁ o₂, Spec.RiscvChoices sp₁ → Spec.RiscvChoices sp₂ →
      Spec.RiscvCorrect sp₁ o₁ → Spec.RiscvCorrect sp₂ o₂ → Spec.RiscvAgree o₁ o₂ :=
  fun _ _ _ _ c₁ c₂ h₁ h₂ => Proof.riscv_agree_of_choices c₁ c₂ h₁ h₂
-- ANCHOR_END: RiscvClaim

end SoftFloat.RISCV.Claim
