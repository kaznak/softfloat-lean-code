/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Real
import SoftFloat.Core.Spec.Compare

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: MinMax
def minMaxLt (fmt : Format) (a b : Nat) : Prop :=
  valE fmt a < valE fmt b ∨ (classify fmt a = .zero true ∧ classify fmt b = .zero false)

def MinMaxSelectOf (pickLess : Bool) (fmt : Format) (a b : Nat) (r : Nat) : Prop :=
  (r = a ∨ r = b)
  ∧ (minMaxLt fmt a b → r = if pickLess then a else b)
  ∧ (minMaxLt fmt b a → r = if pickLess then b else a)

def MinMaxNaNOf (sp : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  r.1 = sp.propagateNaN op fmt [(fmt, a), (fmt, b)]
  ∧ r.2 = { invalidOperation := isSignalingNaN fmt a || isSignalingNaN fmt b }

def MinMaxPropagateSpecOf (sp : Specialization) (op : NaNOperation) (pickLess : Bool) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  if isNaN fmt a || isNaN fmt b then MinMaxNaNOf sp op fmt a b r
  else MinMaxSelectOf pickLess fmt a b r.1 ∧ r.2 = {}

def MinMaxNumberSpecOf (sp : Specialization) (op : NaNOperation) (pickLess : Bool) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  if isNaN fmt a && isNaN fmt b then MinMaxNaNOf sp op fmt a b r
  else if isNaN fmt a then r.1 = b ∧ r.2 = { invalidOperation := isSignalingNaN fmt a }
  else if isNaN fmt b then r.1 = a ∧ r.2 = { invalidOperation := isSignalingNaN fmt b }
  else MinMaxSelectOf pickLess fmt a b r.1 ∧ r.2 = {}

def MinimumNumberSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MinMaxNumberSpecOf sp .minimumNumber true fmt a b r

def MaximumNumberSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MinMaxNumberSpecOf sp .maximumNumber false fmt a b r

def MinimumSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MinMaxPropagateSpecOf sp .minimum true fmt a b r

def MaximumSpecOf (sp : Specialization) (fmt : Format) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  MinMaxPropagateSpecOf sp .maximum false fmt a b r
-- ANCHOR_END: MinMax

end SoftFloat.Spec
