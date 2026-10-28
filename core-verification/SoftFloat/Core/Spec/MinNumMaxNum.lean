/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.MinMax
import SoftFloat.Core.Spec.MinMaxMagnitude

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: MinNumMaxNum
def MinNumMaxNumSelectOf (sp : Specialization) (eq : MinNumMaxNumOperation) (pickLess : Bool) (fmt : Format)
    (a b r : Nat) : Prop :=
  (valE fmt a < valE fmt b → r = if pickLess then a else b)
  ∧ (valE fmt b < valE fmt a → r = if pickLess then b else a)
  ∧ (valE fmt a = valE fmt b → r = sp.minNumMaxNumOfEqual eq fmt a b)

def MinNumMaxNumSpecOf (sp : Specialization) (op : NaNOperation) (eq : MinNumMaxNumOperation) (pickLess : Bool)
    (fmt : Format) (a b : Nat) (r : Nat × StatusFlags) : Prop :=
  if isSignalingNaN fmt a || isSignalingNaN fmt b then
    fmt.IsEncoding r.1 ∧ r.1 = sp.propagateNaN op fmt [(fmt, a), (fmt, b)]
    ∧ r.2 = { invalidOperation := true }
  else if isNaN fmt a || isNaN fmt b then MinMaxNumberSpecOf sp op pickLess fmt a b r
  else fmt.IsEncoding r.1 ∧ MinNumMaxNumSelectOf sp eq pickLess fmt a b r.1 ∧ r.2 = {}

def MinNumSpecOf (sp : Specialization) (fmt : Format) (a b : Nat) (r : Nat × StatusFlags) : Prop :=
  MinNumMaxNumSpecOf sp .minNum .minNum true fmt a b r

def MaxNumSpecOf (sp : Specialization) (fmt : Format) (a b : Nat) (r : Nat × StatusFlags) : Prop :=
  MinNumMaxNumSpecOf sp .maxNum .maxNum false fmt a b r

def MinNumMagSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf true fmt a b (MinNumMaxNumSpecOf sp .minNumMag .minNumMag true fmt a b) r

def MaxNumMagSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MagnitudeSelectOf false fmt a b (MinNumMaxNumSpecOf sp .maxNumMag .maxNumMag false fmt a b) r
-- ANCHOR_END: MinNumMaxNum

end SoftFloat.Spec
