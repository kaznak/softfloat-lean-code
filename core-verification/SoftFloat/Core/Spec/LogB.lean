/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Result
import SoftFloat.Core.Spec.Convert

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: LogBScaleB
def logBRange (fmt : Format) : Int := 2 * (emax fmt + fmt.sigBits)

def IsLogBSpecialValue (fmt : Format) (w : Nat) (v : Int) : Prop :=
  2 * (emax fmt + fmt.sigBits - 1) < |v| ∧ intRangeLo true w ≤ v ∧ v ≤ intRangeHi true w

def LogBFormat.Valid (fmt : Format) : LogBFormat → Prop
  | .sourceFormat => logBRange fmt ≤ 2 ^ fmt.sigBits
  | .integer w nanValue infinityValue zeroValue =>
    intRangeLo true w ≤ -logBRange fmt ∧ logBRange fmt ≤ intRangeHi true w
    ∧ IsLogBSpecialValue fmt w nanValue ∧ IsLogBSpecialValue fmt w infinityValue
    ∧ IsLogBSpecialValue fmt w zeroValue

def IsTwosComplementOf (w n : Nat) (N : Int) : Prop :=
  intRangeLo true w ≤ N ∧ N ≤ intRangeHi true w ∧ (N % (2 ^ w : Int)).toNat = n

def ScaleBOperandValid (fmt : Format) : LogBFormat → Nat → Prop
  | .sourceFormat, n => fmt.IsEncoding n ∧ (isNaN fmt n ∨ IsFinite fmt n ∧ ∃ N : Int, valR fmt n = N)
  | .integer w _ _ _, n => n < 2 ^ w

noncomputable def logBExponent (fmt : Format) (x : Nat) : Int :=
  Int.log 2 |valR fmt x|

noncomputable def LogBSpecOf (sp : Specialization) (fmt : Format) (lf : LogBFormat) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  match lf with
  | .sourceFormat =>
    fmt.IsEncoding r.1 ∧
    match classify fmt x with
    | .quietNaN | .signalingNaN =>
      r.1 = sp.propagateNaN .logB fmt [(fmt, x)] ∧ r.2 = { invalidOperation := isSignalingNaN fmt x }
    | .infinity _ => classify fmt r.1 = .infinity false ∧ r.2 = {}
    | .zero _ => classify fmt r.1 = .infinity true ∧ r.2 = { divideByZero := true }
    | .normal _ | .subnormal _ =>
      IsFinite fmt r.1 ∧ valR fmt r.1 = logBExponent fmt x
      ∧ (logBExponent fmt x = 0 → classify fmt r.1 = .zero false) ∧ r.2 = {}
  | .integer w nanValue infinityValue zeroValue =>
    match classify fmt x with
    | .quietNaN | .signalingNaN => r = ((nanValue % (2 ^ w : Int)).toNat, { invalidOperation := true })
    | .infinity _ => r = ((infinityValue % (2 ^ w : Int)).toNat, { invalidOperation := true })
    | .zero _ => r = ((zeroValue % (2 ^ w : Int)).toNat, { invalidOperation := true })
    | .normal _ | .subnormal _ => r = ((logBExponent fmt x % (2 ^ w : Int)).toNat, {})

noncomputable def scaleBNumberOf (sp : Specialization) (fmt : Format) (rm : RoundingDirection)
    (x : Nat) (N : Int) (r : Nat × StatusFlags) : Prop :=
  match classify fmt x with
  | .quietNaN | .signalingNaN => False
  | .infinity s => classify fmt r.1 = .infinity s ∧ r.2 = {}
  | .normal s | .subnormal s | .zero s => RoundedResultOf sp fmt rm (valR fmt x * 2 ^ N) s r

noncomputable def ScaleBSpecOf (sp : Specialization) (fmt : Format) (lf : LogBFormat)
    (rm : RoundingDirection) (x n : Nat) (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  match lf with
  | .sourceFormat =>
    if isNaN fmt x then
      r.1 = sp.propagateNaN .scaleB fmt [(fmt, x), (fmt, n)]
      ∧ r.2 = { invalidOperation := isSignalingNaN fmt x || isSignalingNaN fmt n }
    else if isNaN fmt n then r = sp.scaleBOfNaNExponent fmt rm x n
    else IsFinite fmt n → ∀ N : Int, valR fmt n = N → scaleBNumberOf sp fmt rm x N r
  | .integer w _ _ _ =>
    if isNaN fmt x then
      r.1 = sp.propagateNaN .scaleB fmt [(fmt, x)] ∧ r.2 = { invalidOperation := isSignalingNaN fmt x }
    else ∀ N : Int, IsTwosComplementOf w n N → scaleBNumberOf sp fmt rm x N r
-- ANCHOR_END: LogBScaleB

end SoftFloat.Spec
