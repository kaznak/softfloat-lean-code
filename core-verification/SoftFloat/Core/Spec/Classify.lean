/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Classify
inductive FloatClass where
  | quietNaN
  | signalingNaN
  | infinity (sign : Bool)
  | normal (sign : Bool)
  | subnormal (sign : Bool)
  | zero (sign : Bool)
  deriving DecidableEq, Repr

def classify (fmt : Format) (bits : Nat) : FloatClass :=
  let u := fmt.unpack bits
  if u.expField = fmt.expMax then
    if u.fracField ≠ 0 then
      if u.fracField ≥ 2 ^ (fmt.fracBits - 1) then .quietNaN else .signalingNaN
    else .infinity u.sign
  else if u.expField ≠ 0 then .normal u.sign
  else if u.fracField ≠ 0 then .subnormal u.sign
  else .zero u.sign

def FloatClass.toClass : FloatClass → Class
  | .quietNaN => .quietNaN
  | .signalingNaN => .signalingNaN
  | .infinity s => if s then .negativeInfinity else .positiveInfinity
  | .normal s => if s then .negativeNormal else .positiveNormal
  | .subnormal s => if s then .negativeSubnormal else .positiveSubnormal
  | .zero s => if s then .negativeZero else .positiveZero

def ClassSpecOf (fmt : Format) (x : Nat) (r : Class) : Prop :=
  r = (classify fmt x).toClass
-- ANCHOR_END: Classify

end SoftFloat.Spec
