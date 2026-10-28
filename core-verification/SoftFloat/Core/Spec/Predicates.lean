/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Spec.Classify

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Predicates
def IsSignMinusSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = (fmt.unpack x).sign

def IsNormalSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ ∃ s, classify fmt x = .normal s

def IsFiniteSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ ∃ s, classify fmt x = .zero s ∨ classify fmt x = .subnormal s
    ∨ classify fmt x = .normal s

def IsZeroSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ ∃ s, classify fmt x = .zero s

def IsSubnormalSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ ∃ s, classify fmt x = .subnormal s

def IsInfiniteSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ ∃ s, classify fmt x = .infinity s

def IsNaNSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ classify fmt x = .quietNaN ∨ classify fmt x = .signalingNaN

def IsSignalingSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ classify fmt x = .signalingNaN

def IsCanonicalSpecOf (fmt : Format) (x : Nat) (r : Bool) : Prop :=
  r = true ↔ fmt.IsEncoding x

def RadixSpecOf (_fmt : Format) (_x : Nat) (r : Nat) : Prop :=
  r = 2
-- ANCHOR_END: Predicates

end SoftFloat.Spec
