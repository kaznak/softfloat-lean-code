/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Round

namespace SoftFloat

-- ANCHOR: convertFormat
namespace Format

def convertFormat (spec : Specialization) (src dst : Format) (rm : RoundingDirection) (a : Nat) : Nat × StatusFlags :=
  let ua := src.unpack a
  if src.isNaNU ua then
    (spec.propagateNaN .convertFormat dst [(src, a)], { invalidOperation := src.isSNaNU ua })
  else if src.isInfU ua then
    (dst.pack ua.sign dst.expMax 0, {})
  else if isZeroU ua then
    (dst.pack ua.sign 0 0, {})
  else
    dst.roundPack spec rm ua.sign (src.sigOf ua) (src.ulpExpOf ua)

end Format
-- ANCHOR_END: convertFormat

-- ANCHOR: convertFromInt
namespace Format

def convertFromInt (spec : Specialization) (fmt : Format) (rm : RoundingDirection) (v : Int) : Nat × StatusFlags :=
  if v = 0 then (fmt.pack false 0 0, {})
  else fmt.roundPack spec rm (v < 0) v.natAbs 0

end Format
-- ANCHOR_END: convertFromInt

-- ANCHOR: convertToInteger
namespace Format

def convertToInteger (spec : Specialization) (fmt : Format) (rm : RoundingDirection)
    (exact signed : Bool) (w : Nat) (a : Nat) : Nat × StatusFlags :=
  let ua := fmt.unpack a
  let invalid : Nat × StatusFlags := (spec.intOutOfRange fmt rm exact signed w a, { invalidOperation := true })
  if fmt.isNaNU ua then invalid
  else if fmt.isInfU ua then invalid
  else
    let m := fmt.sigOf ua
    let q := fmt.ulpExpOf ua
    let (z, inexact) :=
      if 0 ≤ q then
        ((m <<< q.toNat : Nat), false)
      else
        let d := 2 ^ (-q).toNat
        let quot := m / d
        let rem := m % d
        (if roundIncr rm ua.sign quot rem d then quot + 1 else quot, rem != 0)
    let v : Int := if ua.sign then -(z : Int) else (z : Int)
    let lo : Int := if signed then -(2 ^ (w - 1) : Int) else 0
    let hi : Int := if signed then (2 ^ (w - 1) : Int) - 1 else (2 ^ w : Int) - 1
    if v < lo then invalid
    else if hi < v then invalid
    else ((if ua.sign then (2 ^ w - z) % 2 ^ w else z), { inexact := exact && inexact })

end Format
-- ANCHOR_END: convertToInteger

-- ANCHOR: roundToIntegral
namespace Format

def roundToIntegral (spec : Specialization) (fmt : Format) (rm : RoundingDirection) (exact : Bool) (a : Nat) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  if fmt.isNaNU ua then
    (spec.propagateNaN (.roundToIntegral rm exact) fmt [(fmt, a)], { invalidOperation := fmt.isSNaNU ua })
  else if isZeroU ua then
    (a, {})
  else if fmt.expMax ≤ ua.expField then
    (a, {})
  else if fmt.bias + fmt.fracBits ≤ ua.expField then
    (a, {})
  else
    let m := fmt.sigOf ua
    let q := fmt.ulpExpOf ua
    let d := 2 ^ (-q).toNat
    let quot := m / d
    let rem := m % d
    let z := if roundIncr rm ua.sign quot rem d then quot + 1 else quot
    if z = 0 then
      (fmt.pack ua.sign 0 0, { inexact := exact && rem != 0 })
    else
      let (r, _) := fmt.roundPack spec rm ua.sign z 0
      (r, { inexact := exact && rem != 0 })

end Format
-- ANCHOR_END: roundToIntegral

end SoftFloat
