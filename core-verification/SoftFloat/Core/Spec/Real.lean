/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Spec.Classify
import Mathlib

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Value
def emax (fmt : Format) : Int := fmt.bias

def emin (fmt : Format) : Int := 1 - emax fmt

noncomputable def valR (fmt : Format) (bits : Nat) : ℝ :=
  let u := fmt.unpack bits
  let s : ℝ := if u.sign then -1 else 1
  let t : ℝ := (2 : ℝ) ^ (1 - (fmt.sigBits : Int)) * (u.fracField : ℝ)
  match classify fmt bits with
  | .normal _ => s * (2 : ℝ) ^ ((u.expField : Int) - (fmt.bias : Int)) * (1 + t)
  | .subnormal _ | .zero _ => s * (2 : ℝ) ^ emin fmt * (0 + t)
  | .quietNaN | .signalingNaN | .infinity _ => 0
-- ANCHOR_END: Value

-- ANCHOR: Rounding
noncomputable def roundMagDown (x : ℝ) : Int := ⌊x⌋

noncomputable def roundMagUp (x : ℝ) : Int := ⌈x⌉

noncomputable def roundMagTiesToEven (x : ℝ) : Int :=
  let fl := ⌊x⌋
  let fr := x - fl
  if fr < 1/2 then fl
  else if 1/2 < fr then fl + 1
  else if fl % 2 = 0 then fl else fl + 1

noncomputable def roundMagTiesToAway (x : ℝ) : Int :=
  let fl := ⌊x⌋
  if 1/2 ≤ x - fl then fl + 1 else fl

noncomputable def roundMagToOdd (x : ℝ) : Int :=
  let fl := ⌊x⌋
  if x = fl then fl else if fl % 2 = 0 then fl + 1 else fl

noncomputable def roundAbs (rm : RoundingDirection) (negative : Bool) (x : ℝ) : Int :=
  match rm with
  | .roundTiesToEven   => roundMagTiesToEven x
  | .roundTiesToAway => roundMagTiesToAway x
  | .roundTowardZero     => roundMagDown x
  | .roundTowardNegative        => if negative then roundMagUp x else roundMagDown x
  | .roundTowardPositive        => if negative then roundMagDown x else roundMagUp x
  | .roundToOdd        => roundMagToOdd x

noncomputable def magR (x : ℝ) : Int := Int.log 2 |x| + 1

noncomputable def cexpR (fmt : Format) (x : ℝ) : Int :=
  Max.max (magR x - (fmt.sigBits : Int)) fmt.minQ

noncomputable def roundR (fmt : Format) (rm : RoundingDirection) (x : ℝ) : ℝ :=
  (if x < 0 then -1 else 1)
    * ((roundAbs rm (decide (x < 0)) (|x| / (2 : ℝ) ^ cexpR fmt x) : Int) : ℝ)
    * (2 : ℝ) ^ cexpR fmt x

noncomputable def cexpRInf (fmt : Format) (x : ℝ) : Int :=
  magR x - (fmt.sigBits : Int)

noncomputable def roundRInf (fmt : Format) (rm : RoundingDirection) (x : ℝ) : ℝ :=
  (if x < 0 then -1 else 1)
    * ((roundAbs rm (decide (x < 0)) (|x| / (2 : ℝ) ^ cexpRInf fmt x) : Int) : ℝ)
    * (2 : ℝ) ^ cexpRInf fmt x

noncomputable def ovfThreshold (fmt : Format) : ℝ := (2 : ℝ) ^ (emax fmt + 1)
-- ANCHOR_END: Rounding

end SoftFloat.Spec
