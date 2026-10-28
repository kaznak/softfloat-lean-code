/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Result
import SoftFloat.Core.Spec.Sign

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Arith
def arithSign (fmt : Format) (x : Nat) : Bool :=
  match classify fmt x with
  | .infinity s | .normal s | .subnormal s | .zero s => s
  | _ => false

def arithIsInf (fmt : Format) (x : Nat) : Bool :=
  match classify fmt x with
  | .infinity _ => true
  | _ => false

def arithIsZero (fmt : Format) (x : Nat) : Bool :=
  match classify fmt x with
  | .zero _ => true
  | _ => false

def arithZeroSumNegative (rm : RoundingDirection) (sa sb : Bool) : Bool :=
  if sa = sb then sa else decide (rm = .roundTowardNegative)

def arithSumOf (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat)
    (sb : Bool) (vb : ℝ) (nan : Nat) (r : Nat × StatusFlags) : Prop :=
  dst.IsEncoding r.1 ∧
  if isNaN fa a || isNaN fb b then
    r.1 = nan ∧ r.2 = { invalidOperation := isSignalingNaN fa a || isSignalingNaN fb b }
  else if arithIsInf fa a && arithIsInf fb b && arithSign fa a != sb then
    r.1 = nan ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fa a then
    classify dst r.1 = .infinity (arithSign fa a) ∧ r.2 = {}
  else if arithIsInf fb b then
    classify dst r.1 = .infinity sb ∧ r.2 = {}
  else
    RoundedResultOf sp dst rm (valR fa a + vb) (arithZeroSumNegative rm (arithSign fa a) sb) r

def AdditionSpecOf (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  arithSumOf sp fa fb dst rm a b (arithSign fb b) (valR fb b)
    (sp.propagateNaN .addition dst [(fa, a), (fb, b)]) r

def SubtractionSpecOf (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  arithSumOf sp fa fb dst rm a b (!arithSign fb b) (-valR fb b)
    (sp.propagateNaN .subtraction dst [(fa, a), (fb, b)]) r

def MultiplicationSpecOf (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  let nan := sp.propagateNaN .multiplication dst [(fa, a), (fb, b)]
  let sign := arithSign fa a != arithSign fb b
  dst.IsEncoding r.1 ∧
  if isNaN fa a || isNaN fb b then
    r.1 = nan ∧ r.2 = { invalidOperation := isSignalingNaN fa a || isSignalingNaN fb b }
  else if (arithIsInf fa a && arithIsZero fb b) || (arithIsZero fa a && arithIsInf fb b) then
    r.1 = nan ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fa a || arithIsInf fb b then
    classify dst r.1 = .infinity sign ∧ r.2 = {}
  else
    RoundedResultOf sp dst rm (valR fa a * valR fb b) sign r

def DivisionSpecOf (sp : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat)
    (r : Nat × StatusFlags) : Prop :=
  let nan := sp.propagateNaN .division dst [(fa, a), (fb, b)]
  let sign := arithSign fa a != arithSign fb b
  dst.IsEncoding r.1 ∧
  if isNaN fa a || isNaN fb b then
    r.1 = nan ∧ r.2 = { invalidOperation := isSignalingNaN fa a || isSignalingNaN fb b }
  else if (arithIsInf fa a && arithIsInf fb b) || (arithIsZero fa a && arithIsZero fb b) then
    r.1 = nan ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fa a then
    classify dst r.1 = .infinity sign ∧ r.2 = {}
  else if arithIsInf fb b then
    classify dst r.1 = .zero sign ∧ r.2 = {}
  else if arithIsZero fb b then
    classify dst r.1 = .infinity sign ∧ r.2 = { divideByZero := true }
  else
    RoundedResultOf sp dst rm (valR fa a / valR fb b) sign r

def SquareRootSpecOf (sp : Specialization) (fa dst : Format) (rm : RoundingDirection) (a : Nat)
    (r : Nat × StatusFlags) : Prop :=
  let nan := sp.propagateNaN .squareRoot dst [(fa, a)]
  dst.IsEncoding r.1 ∧
  if isNaN fa a then
    r.1 = nan ∧ r.2 = { invalidOperation := isSignalingNaN fa a }
  else if arithIsZero fa a then
    classify dst r.1 = .zero (arithSign fa a) ∧ r.2 = {}
  else if arithSign fa a then
    r.1 = nan ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fa a then
    classify dst r.1 = .infinity false ∧ r.2 = {}
  else
    RoundedResultOf sp dst rm (Real.sqrt (valR fa a)) false r

def FusedMultiplyAddSpecOf (sp : Specialization) (fa fb fc dst : Format) (rm : RoundingDirection)
    (a b c : Nat) (r : Nat × StatusFlags) : Prop :=
  let sab := arithSign fa a != arithSign fb b
  let zeroTimesInf := (arithIsInf fa a && arithIsZero fb b) || (arithIsZero fa a && arithIsInf fb b)
  let nan := sp.propagateNaN .fusedMultiplyAdd dst [(fa, a), (fb, b), (fc, c)]
  dst.IsEncoding r.1 ∧
  if isNaN fa a || isNaN fb b then
    r.1 = nan
    ∧ r.2 = { invalidOperation := isSignalingNaN fa a || isSignalingNaN fb b || isSignalingNaN fc c }
  else if isNaN fc c then
    if zeroTimesInf then
      r.1 = nan
      ∧ r.2 = { invalidOperation := isSignalingNaN fc c || sp.fusedMultiplyAddZeroInfinityQuietNaNInvalid }
    else
      r.1 = nan ∧ r.2 = { invalidOperation := isSignalingNaN fc c }
  else if zeroTimesInf then
    r.1 = nan ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fa a || arithIsInf fb b then
    if arithIsInf fc c && arithSign fc c != sab then
      r.1 = nan ∧ r.2 = { invalidOperation := true }
    else
      classify dst r.1 = .infinity sab ∧ r.2 = {}
  else if arithIsInf fc c then
    classify dst r.1 = .infinity (arithSign fc c) ∧ r.2 = {}
  else
    RoundedResultOf sp dst rm (valR fa a * valR fb b + valR fc c)
      (arithZeroSumNegative rm sab (arithSign fc c)) r
-- ANCHOR_END: Arith

end SoftFloat.Spec
