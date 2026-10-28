/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Encoding

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Spec

variable (sp : Specialization)

theorem softfloat_copy_spec :
    ∀ fmt x, CopySpecOf fmt x ((softfloat sp).copy fmt x) :=
  fun _ _ => rfl

theorem softfloat_negate_spec :
    ∀ fmt x, x < 2 ^ fmt.width → NegateSpecOf fmt x ((softfloat sp).negate fmt x) :=
  fun fmt _ hx => flipSign_eq_withSign fmt hx

theorem softfloat_abs_spec :
    ∀ fmt x, x < 2 ^ fmt.width → AbsSpecOf fmt x ((softfloat sp).abs fmt x) :=
  fun fmt _ hx => clearSign_eq_withSign fmt hx

theorem softfloat_copySign_spec :
    ∀ fmt x y, x < 2 ^ fmt.width → y < 2 ^ fmt.width →
      CopySignSpecOf fmt x y ((softfloat sp).copySign fmt x y) :=
  fun fmt _ y hx _ => copySign_eq_withSign fmt hx y

theorem softfloat_classOf_spec :
    ∀ fmt x, ClassSpecOf fmt x ((softfloat sp).classOf fmt x) :=
  classSpecOf_classOf

end SoftFloat.Proof
