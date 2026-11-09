/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Correctness
import SoftFloat.Core.Proof.Uniqueness
import SoftFloat.FloatLib.Spec.Agree

/-!
# From meeting the specification to agreement

If the operations of FloatLib meet the specification of Core with a valid specialization `sp`,
then the operations of Core with `sp` compute what FloatLib computes. The group `hybrid sp` is
the operations of Core with `sp` in which the six compared operations, on the range compared,
are those of FloatLib; it is correct, and by the uniqueness of correct groups it agrees with
`softfloat sp`.
-/

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.FloatLib.Spec

/-- The operations of Core with `sp`, with those of FloatLib on the range compared. -/
def hybrid (sp : Specialization) : Ops :=
  { softfloat sp with
    addition := fun fa fb dst rm a b =>
      if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flAdd dst a b
      else (softfloat sp).addition fa fb dst rm a b
    subtraction := fun fa fb dst rm a b =>
      if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flSub dst a b
      else (softfloat sp).subtraction fa fb dst rm a b
    multiplication := fun fa fb dst rm a b =>
      if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flMul dst a b
      else (softfloat sp).multiplication fa fb dst rm a b
    division := fun fa fb dst rm a b =>
      if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flDiv dst a b
      else (softfloat sp).division fa fb dst rm a b
    squareRoot := fun fa dst rm a =>
      if fa = dst ∧ rm = .roundTiesToEven then flSqrt dst a
      else (softfloat sp).squareRoot fa dst rm a
    fusedMultiplyAdd := fun fa fb fc dst rm a b c =>
      if fa = dst ∧ fb = dst ∧ fc = dst ∧ rm = .roundTiesToEven then flFma dst a b c
      else (softfloat sp).fusedMultiplyAdd fa fb fc dst rm a b c }

theorem hybrid_correct {sp : Specialization} (hv : Specialization.Valid sp) (hm : FloatLibMeetsSpec sp) :
    Correct sp (hybrid sp) :=
  have hs := softfloat_correct sp hv
  { hs with
    addition := fun fa fb dst rm a b h => by
      show AdditionSpecOf sp fa fb dst rm a b
        (if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flAdd dst a b
         else (softfloat sp).addition fa fb dst rm a b)
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hm.addition _ a b h.1 h.2
      · exact hs.addition fa fb dst rm a b h
    subtraction := fun fa fb dst rm a b h => by
      show SubtractionSpecOf sp fa fb dst rm a b
        (if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flSub dst a b
         else (softfloat sp).subtraction fa fb dst rm a b)
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hm.subtraction _ a b h.1 h.2
      · exact hs.subtraction fa fb dst rm a b h
    multiplication := fun fa fb dst rm a b h => by
      show MultiplicationSpecOf sp fa fb dst rm a b
        (if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flMul dst a b
         else (softfloat sp).multiplication fa fb dst rm a b)
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hm.multiplication _ a b h.1 h.2
      · exact hs.multiplication fa fb dst rm a b h
    division := fun fa fb dst rm a b h => by
      show DivisionSpecOf sp fa fb dst rm a b
        (if fa = dst ∧ fb = dst ∧ rm = .roundTiesToEven then flDiv dst a b
         else (softfloat sp).division fa fb dst rm a b)
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        exact hm.division _ a b h.1 h.2
      · exact hs.division fa fb dst rm a b h
    squareRoot := fun fa dst rm a h => by
      show SquareRootSpecOf sp fa dst rm a
        (if fa = dst ∧ rm = .roundTiesToEven then flSqrt dst a
         else (softfloat sp).squareRoot fa dst rm a)
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc
        exact hm.squareRoot _ a h
      · exact hs.squareRoot fa dst rm a h
    fusedMultiplyAdd := fun fa fb fc dst rm a b c h => by
      show FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c
        (if fa = dst ∧ fb = dst ∧ fc = dst ∧ rm = .roundTiesToEven then flFma dst a b c
         else (softfloat sp).fusedMultiplyAdd fa fb fc dst rm a b c)
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        exact hm.fusedMultiplyAdd _ a b c h.1 h.2.1 h.2.2
      · exact hs.fusedMultiplyAdd fa fb fc dst rm a b c h }

-- ANCHOR: AgreeOfMeetsSpec
theorem agree_of_meetsSpec {sp : Specialization} (hv : Specialization.Valid sp)
    (hm : FloatLibMeetsSpec sp) : FloatLibAgree (softfloat sp) := by
  have ha := correct_agree (softfloat_correct sp hv) (hybrid_correct hv hm)
  refine ⟨fun fmt a b h₁ h₂ => ?_, fun fmt a b h₁ h₂ => ?_, fun fmt a b h₁ h₂ => ?_,
    fun fmt a b h₁ h₂ => ?_, fun fmt a h₁ => ?_, fun fmt a b c h₁ h₂ h₃ => ?_⟩
  · have := ha.addition fmt fmt fmt .roundTiesToEven a b ⟨h₁, h₂⟩
    simpa [hybrid] using this
  · have := ha.subtraction fmt fmt fmt .roundTiesToEven a b ⟨h₁, h₂⟩
    simpa [hybrid] using this
  · have := ha.multiplication fmt fmt fmt .roundTiesToEven a b ⟨h₁, h₂⟩
    simpa [hybrid] using this
  · have := ha.division fmt fmt fmt .roundTiesToEven a b ⟨h₁, h₂⟩
    simpa [hybrid] using this
  · have := ha.squareRoot fmt fmt .roundTiesToEven a h₁
    simpa [hybrid] using this
  · have := ha.fusedMultiplyAdd fmt fmt fmt fmt .roundTiesToEven a b c ⟨h₁, h₂, h₃⟩
    simpa [hybrid] using this
-- ANCHOR_END: AgreeOfMeetsSpec

end SoftFloat.FloatLib.Proof
