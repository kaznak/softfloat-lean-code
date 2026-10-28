/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Sign
import SoftFloat.Core.Spec.MinMax

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: MinMaxMagnitude
def magnitudeLt (fmt : Format) (a b : Nat) : Prop :=
  isNaN fmt a = false ∧ isNaN fmt b = false
  ∧ valE fmt (withSign fmt a false) < valE fmt (withSign fmt b false)

def MagnitudeSelectOf (pickLess : Bool) (fmt : Format) (a b : Nat)
    (otherwise : Nat × StatusFlags → Prop) (r : Nat × StatusFlags) : Prop :=
  (magnitudeLt fmt a b → r = (if pickLess then a else b, {}))
  ∧ (magnitudeLt fmt b a → r = (if pickLess then b else a, {}))
  ∧ (¬ magnitudeLt fmt a b → ¬ magnitudeLt fmt b a → otherwise r)

def MinimumMagnitudeSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf true fmt a b (MinMaxPropagateSpecOf sp .minimumMagnitude true fmt a b) r

def MinimumMagnitudeNumberSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf true fmt a b (MinMaxNumberSpecOf sp .minimumMagnitudeNumber true fmt a b) r

def MaximumMagnitudeSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf false fmt a b (MinMaxPropagateSpecOf sp .maximumMagnitude false fmt a b) r

def MaximumMagnitudeNumberSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf false fmt a b (MinMaxNumberSpecOf sp .maximumMagnitudeNumber false fmt a b) r
-- ANCHOR_END: MinMaxMagnitude

end SoftFloat.Spec
