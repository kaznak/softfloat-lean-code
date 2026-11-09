/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.FloatLib.Spec.Choices
import SoftFloat.FloatLib.Spec.Agree
import SoftFloat.FloatLib.Operators
import SoftFloat.FloatLib.Proof.Specialization
import SoftFloat.FloatLib.Proof.Hybrid
import SoftFloat.FloatLib.Proof.AddFinite
import SoftFloat.FloatLib.Proof.SubFinite
import SoftFloat.FloatLib.Proof.MulFinite
import SoftFloat.FloatLib.Proof.DivFinite
import SoftFloat.FloatLib.Proof.SqrtFinite
import SoftFloat.FloatLib.Proof.FmaFinite

namespace SoftFloat.FloatLib.Claim

open SoftFloat

-- ANCHOR: FloatLibClaim
/-- On every bit string of every format, the six operations of FloatLib compared, rounded to
nearest with ties to even, meet the specification of Core with every specialization that has
the choices of FloatLib. -/
theorem meetsSpec : ∀ sp, Spec.FloatLibChoices sp → Spec.FloatLibMeetsSpec sp :=
  fun sp hc =>
    { addition := fun _ _ _ ha hb => Proof.floatlib_add_meets_spec sp hc ha hb
      subtraction := fun _ _ _ ha hb => Proof.floatlib_sub_meets_spec sp hc ha hb
      multiplication := fun _ _ _ ha hb => Proof.floatlib_mul_meets_spec sp hc ha hb
      division := fun _ _ _ ha hb => Proof.floatlib_div_meets_spec sp hc ha hb
      squareRoot := fun _ _ ha => Proof.floatlib_sqrt_meets_spec sp hc ha
      fusedMultiplyAdd := fun _ _ _ _ ha hb hc' => Proof.floatlib_fma_meets_spec sp hc ha hb hc' }

/-- There, the operations of Core with a valid specialization that has the choices of FloatLib
compute what FloatLib computes, bit for bit and flag for flag. -/
theorem agreement :
    ∀ sp, SoftFloat.Spec.Specialization.Valid sp → Spec.FloatLibChoices sp →
      Spec.FloatLibAgree (softfloat sp) :=
  fun sp hv hc => Proof.agree_of_meetsSpec hv (meetsSpec sp hc)

/-- Such a specialization exists: `Specialization.floatlib`. -/
theorem witness :
    SoftFloat.Spec.Specialization.Valid Specialization.floatlib ∧
      Spec.FloatLibChoices Specialization.floatlib :=
  ⟨Proof.floatlib_valid, Proof.floatlib_choices⟩
-- ANCHOR_END: FloatLibClaim

end SoftFloat.FloatLib.Claim
