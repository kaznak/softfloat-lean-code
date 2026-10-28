/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Round
import SoftFloat.Core.Operators.Convert

namespace SoftFloat

-- ANCHOR: LogBScaleB
namespace Format

def toTwosComplement (w : Nat) (v : Int) : Nat :=
  (v % (2 ^ w : Int)).toNat

def ofTwosComplement (w n : Nat) : Int :=
  if n < 2 ^ (w - 1) then n else (n : Int) - 2 ^ w

def exponentOfU (fmt : Format) (u : Unpacked) : Int :=
  fmt.ulpExpOf u + (Nat.log2 (fmt.sigOf u) : Int)

def integralValueU (fmt : Format) (u : Unpacked) : Int :=
  let q := fmt.ulpExpOf u
  let z : Nat := if 0 ≤ q then fmt.sigOf u <<< q.toNat else fmt.sigOf u >>> (-q).toNat
  if u.sign then -(z : Int) else (z : Int)

def scaleBLimit (fmt : Format) : Int :=
  2 * ((fmt.bias : Int) + (fmt.sigBits : Int))

def logB (spec : Specialization) (fmt : Format) (lf : LogBFormat) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  match lf with
  | .sourceFormat =>
    if fmt.isNaNU u then
      (spec.propagateNaN .logB fmt [(fmt, a)], { invalidOperation := fmt.isSNaNU u })
    else if fmt.isInfU u then (fmt.pack false fmt.expMax 0, {})
    else if isZeroU u then (fmt.pack true fmt.expMax 0, { divideByZero := true })
    else ((fmt.convertFromInt spec .roundTiesToEven (fmt.exponentOfU u)).1, {})
  | .integer w nanValue infinityValue zeroValue =>
    if fmt.isNaNU u then (toTwosComplement w nanValue, { invalidOperation := true })
    else if fmt.isInfU u then (toTwosComplement w infinityValue, { invalidOperation := true })
    else if isZeroU u then (toTwosComplement w zeroValue, { invalidOperation := true })
    else (toTwosComplement w (fmt.exponentOfU u), {})

def scaleBNumber (spec : Specialization) (fmt : Format) (rm : RoundingDirection) (u : Unpacked)
    (N : Int) : Nat × StatusFlags :=
  if fmt.isInfU u then (fmt.pack u.sign fmt.expMax 0, {})
  else if isZeroU u then (fmt.pack u.sign 0 0, {})
  else fmt.roundPack spec rm u.sign (fmt.sigOf u) (fmt.ulpExpOf u + Max.max N (-fmt.scaleBLimit))

def scaleB (spec : Specialization) (fmt : Format) (lf : LogBFormat) (rm : RoundingDirection)
    (a n : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  match lf with
  | .sourceFormat =>
    let v := fmt.unpack n
    if fmt.isNaNU u then
      (spec.propagateNaN .scaleB fmt [(fmt, a), (fmt, n)],
        { invalidOperation := fmt.isSNaNU u || fmt.isSNaNU v })
    else if fmt.isNaNU v then spec.scaleBOfNaNExponent fmt rm a n
    else fmt.scaleBNumber spec rm u (fmt.integralValueU v)
  | .integer w _ _ _ =>
    if fmt.isNaNU u then
      (spec.propagateNaN .scaleB fmt [(fmt, a)], { invalidOperation := fmt.isSNaNU u })
    else fmt.scaleBNumber spec rm u (ofTwosComplement w n)

end Format
-- ANCHOR_END: LogBScaleB

end SoftFloat
