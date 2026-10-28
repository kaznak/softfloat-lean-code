/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Result

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Convert
def convertNaNResultOf (sp : Specialization) (src dst : Format) (a : Nat)
    (r : Nat × StatusFlags) : Prop :=
  r.1 = sp.propagateNaN .convertFormat dst [(src, a)] ∧ r.2 = { invalidOperation := isSignalingNaN src a }

def convertExactSpecialOf (fmt : Format) (c : FloatClass) (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧ classify fmt r.1 = c ∧ r.2 = {}

noncomputable def integralPartOf (rm : RoundingDirection) (negative : Bool) (x : ℝ) : Int :=
  (if negative then -1 else 1) * roundAbs rm negative |x|

def integralFlagsOf (exact : Bool) (changed : Prop) (f : StatusFlags) : Prop :=
  (f.inexact = true ↔ exact = true ∧ changed) ∧ f.underflow = false ∧ f.overflow = false
    ∧ f.divideByZero = false ∧ f.invalidOperation = false

def intRangeLo (signed : Bool) (w : Nat) : Int :=
  if signed then -(2 ^ (w - 1) : Int) else 0

def intRangeHi (signed : Bool) (w : Nat) : Int :=
  if signed then (2 ^ (w - 1) : Int) - 1 else (2 ^ w : Int) - 1

def ConvertFormatSpecOf (sp : Specialization) (src dst : Format) (rm : RoundingDirection)
    (a : Nat) (r : Nat × StatusFlags) : Prop :=
  match classify src a with
  | .quietNaN | .signalingNaN => convertNaNResultOf sp src dst a r
  | .infinity s => convertExactSpecialOf dst (.infinity s) r
  | .normal s | .subnormal s | .zero s => RoundedResultOf sp dst rm (valR src a) s r

def ConvertFromIntSpecOf (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (v : Int) (r : Nat × StatusFlags) : Prop :=
  RoundedResultOf sp fmt rm (v : ℝ) false r

def ConvertToIntegerSpecOf (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (exact signed : Bool) (w : Nat) (a : Nat) (r : Nat × StatusFlags) : Prop :=
  let invalid : Nat × StatusFlags := (sp.intOutOfRange fmt rm exact signed w a, { invalidOperation := true })
  match classify fmt a with
  | .quietNaN | .signalingNaN => r = invalid
  | .infinity _ => r = invalid
  | .normal s | .subnormal s | .zero s =>
    let n := integralPartOf rm s (valR fmt a)
    if n < intRangeLo signed w then r = invalid
    else if intRangeHi signed w < n then r = invalid
    else r.1 = (n % (2 ^ w : Int)).toNat ∧ integralFlagsOf exact ((n : ℝ) ≠ valR fmt a) r.2

def RoundToIntegralSpecOf (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (exact : Bool) (a : Nat) (r : Nat × StatusFlags) : Prop :=
  match classify fmt a with
  | .quietNaN | .signalingNaN =>
    r.1 = sp.propagateNaN (.roundToIntegral rm exact) fmt [(fmt, a)] ∧ r.2 = { invalidOperation := isSignalingNaN fmt a }
  | .infinity s => convertExactSpecialOf fmt (.infinity s) r
  | .normal s | .subnormal s | .zero s =>
    let n := integralPartOf rm s (valR fmt a)
    fmt.IsEncoding r.1 ∧ IsFinite fmt r.1 ∧ valR fmt r.1 = n
    ∧ (n = 0 → classify fmt r.1 = .zero s)
    ∧ integralFlagsOf exact ((n : ℝ) ≠ valR fmt a) r.2
-- ANCHOR_END: Convert

end SoftFloat.Spec
