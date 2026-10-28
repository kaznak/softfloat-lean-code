/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof

namespace SoftFloat.Claim

open SoftFloat

-- ANCHOR: Claim
theorem correctness :
    ∀ sp, Spec.Specialization.Valid sp →
      Spec.Correct sp (softfloat sp) ∧ ∀ fmt, Spec.FormatCorrect sp fmt (perFormat (softfloat sp) fmt) :=
  fun sp hsp => ⟨Proof.softfloat_correct sp hsp, Proof.perFormat_correct hsp (Proof.softfloat_correct sp hsp)⟩

theorem uniqueness :
    ∀ sp o₁ o₂, Spec.Specialization.Valid sp → Spec.Correct sp o₁ → Spec.Correct sp o₂ → Spec.Agree o₁ o₂ :=
  fun _ _ _ _ h₁ h₂ => Proof.correct_agree h₁ h₂
-- ANCHOR_END: Claim

end SoftFloat.Claim
