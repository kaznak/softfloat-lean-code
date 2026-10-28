/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Real

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Compare
def isNaN (fmt : Format) (bits : Nat) : Bool :=
  match classify fmt bits with
  | .quietNaN | .signalingNaN => true
  | _ => false

def isSignalingNaN (fmt : Format) (bits : Nat) : Bool :=
  classify fmt bits == .signalingNaN

noncomputable def valE (fmt : Format) (bits : Nat) : EReal :=
  match classify fmt bits with
  | .infinity s => if s then ⊥ else ⊤
  | _ => (valR fmt bits : EReal)

noncomputable def relationOf (fa fb : Format) (a b : Nat) : Relation :=
  if isNaN fa a || isNaN fb b then .unordered
  else if valE fa a < valE fb b then .lessThan
  else if valE fa a = valE fb b then .equal
  else .greaterThan

def ComparisonSpecOf (fa fb : Format) (signaling : Bool) (holds : Relation → Bool) (a b : Nat)
    (r : Bool × StatusFlags) : Prop :=
  r.1 = holds (relationOf fa fb a b)
  ∧ r.2 = { invalidOperation := if signaling then isNaN fa a || isNaN fb b
                       else isSignalingNaN fa a || isSignalingNaN fb b }
-- ANCHOR_END: Compare

end SoftFloat.Spec
