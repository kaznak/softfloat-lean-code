/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Sign
def withSign (fmt : Format) (x : Nat) (s : Bool) : Nat :=
  let u := fmt.unpack x
  fmt.pack s u.expField u.fracField

def CopySpecOf (_fmt : Format) (x : Nat) (r : Nat) : Prop :=
  r = x

def NegateSpecOf (fmt : Format) (x : Nat) (r : Nat) : Prop :=
  r = withSign fmt x (!(fmt.unpack x).sign)

def AbsSpecOf (fmt : Format) (x : Nat) (r : Nat) : Prop :=
  r = withSign fmt x false

def CopySignSpecOf (fmt : Format) (x y : Nat) (r : Nat) : Prop :=
  r = withSign fmt x (fmt.unpack y).sign
-- ANCHOR_END: Sign

end SoftFloat.Spec
