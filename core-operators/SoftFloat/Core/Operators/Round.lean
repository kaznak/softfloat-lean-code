/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: Round
namespace Format

def roundIncr (rm : RoundingDirection) (sign : Bool) (quot rem d : Nat) : Bool :=
  match rm with
  | .roundTiesToEven   => rem * 2 > d || (rem * 2 == d && quot % 2 == 1)
  | .roundTiesToAway => rem * 2 ≥ d
  | .roundTowardZero     => false
  | .roundTowardNegative        => sign && rem != 0
  | .roundTowardPositive        => !sign && rem != 0
  | .roundToOdd        => rem != 0 && quot % 2 == 0

def overflowResult (fmt : Format) (rm : RoundingDirection) (sign : Bool) : Nat × StatusFlags :=
  let inf := fmt.pack sign fmt.expMax 0
  let maxFin := fmt.pack sign (fmt.expMax - 1) (2 ^ fmt.fracBits - 1)
  let r := match rm with
    | .roundTiesToEven | .roundTiesToAway => inf
    | .roundTowardZero | .roundToOdd => maxFin
    | .roundTowardNegative => if sign then inf else maxFin
    | .roundTowardPositive => if sign then maxFin else inf
  (r, { overflow := true, inexact := true })

def roundPack (spec : Specialization) (fmt : Format) (rm : RoundingDirection)
    (sign : Bool) (m : Nat) (q : Int) : Nat × StatusFlags :=
  let bl : Nat := Nat.log2 m + 1
  let E : Int := q + bl - 1
  let U : Int := Max.max (E - fmt.fracBits) fmt.minQ
  let (m', inexact) :=
    if U ≤ q then
      ((m <<< (q - U).toNat, false) : Nat × Bool)
    else
      let d := 2 ^ (U - q).toNat
      let quot := m / d
      let rem := m % d
      (if roundIncr rm sign quot rem d then quot + 1 else quot, rem != 0)
  let (m'', U') :=
    if m' = 2 ^ fmt.sigBits then ((2 ^ fmt.fracBits : Nat), U + 1) else (m', U)
  let Uu : Int := E - fmt.fracBits
  let tiny : Bool :=
    match spec.tininess with
    | .beforeRounding => decide (Uu < fmt.minQ)
    | .afterRounding =>
      if fmt.minQ ≤ Uu then false
      else if Uu ≤ q then true
      else
        let d := 2 ^ (Uu - q).toNat
        let quot := m / d
        let mu := if roundIncr rm sign quot (m % d) d then quot + 1 else quot
        if mu = 2 ^ fmt.sigBits then Uu + 1 < fmt.minQ else true
  if m'' = 0 then
    (fmt.pack sign 0 0, { underflow := true, inexact := true })
  else if m'' < 2 ^ fmt.fracBits then
    (fmt.pack sign 0 m'', { underflow := inexact, inexact })
  else
    let be : Int := U' + fmt.fracBits + fmt.bias
    if fmt.expMax ≤ be then
      fmt.overflowResult rm sign
    else
      (fmt.pack sign be.toNat (m'' - 2 ^ fmt.fracBits), { underflow := inexact && tiny, inexact })

end Format
-- ANCHOR_END: Round

end SoftFloat
