/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Real
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Specialization

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Result
def IsFinite (fmt : Format) (bits : Nat) : Prop :=
  match classify fmt bits with
  | .normal _ | .subnormal _ | .zero _ => True
  | _ => False

noncomputable def maxFinite (fmt : Format) : ℝ :=
  (2 - (2 : ℝ) ^ (1 - (fmt.sigBits : Int))) * (2 : ℝ) ^ emax fmt

def overflowToInfinity (rm : RoundingDirection) (negative : Bool) : Bool :=
  match rm with
  | .roundTiesToEven | .roundTiesToAway => true
  | .roundTowardZero | .roundToOdd => false
  | .roundTowardPositive => !negative
  | .roundTowardNegative => negative

def Tiny (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (x : ℝ) : Prop :=
  x ≠ 0 ∧
  match sp.tininess with
  | .afterRounding => |roundRInf fmt rm x| < (2 : ℝ) ^ emin fmt
  | .beforeRounding => |x| < (2 : ℝ) ^ emin fmt

def RoundedResultOf (sp : Specialization) (fmt : Format) (rm : RoundingDirection) (x : ℝ)
    (zeroNegative : Bool) (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧ r.2.invalidOperation = false ∧ r.2.divideByZero = false ∧
  if maxFinite fmt < |roundR fmt rm x| then
    (if overflowToInfinity rm (decide (x < 0)) then classify fmt r.1 = .infinity (decide (x < 0))
     else IsFinite fmt r.1 ∧ valR fmt r.1 = (if x < 0 then -maxFinite fmt else maxFinite fmt))
    ∧ r.2.overflow = true ∧ r.2.inexact = true ∧ r.2.underflow = false
  else
    IsFinite fmt r.1 ∧ valR fmt r.1 = roundR fmt rm x
    ∧ (roundR fmt rm x = 0 → classify fmt r.1 = .zero (if x = 0 then zeroNegative else decide (x < 0)))
    ∧ r.2.overflow = false
    ∧ (r.2.inexact = true ↔ roundR fmt rm x ≠ x)
    ∧ (r.2.underflow = true ↔ roundR fmt rm x ≠ x ∧ Tiny sp fmt rm x)
-- ANCHOR_END: Result

end SoftFloat.Spec
