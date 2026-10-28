/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Round

namespace SoftFloat

namespace Format

-- ANCHOR: remainder
def remainder (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  let nan := spec.propagateNaN .remainder fmt [(fmt, a), (fmt, b)]
  if fmt.isNaNU ua || fmt.isNaNU ub then
    (nan, { invalidOperation := fmt.isSNaNU ua || fmt.isSNaNU ub })
  else if fmt.isInfU ua || isZeroU ub then
    (nan, { invalidOperation := true })
  else if fmt.isInfU ub then
    (a, {})
  else
    let qa := fmt.ulpExpOf ua
    let qb := fmt.ulpExpOf ub
    let q := Min.min qa qb
    let X := fmt.sigOf ua <<< (qa - q).toNat
    let Y := fmt.sigOf ub <<< (qb - q).toNat
    let t := X % (2 * Y)
    let rem := if Y ≤ t then t - Y else t
    if rem * 2 > Y || (rem * 2 == Y && Y ≤ t) then
      fmt.roundPack spec .roundTiesToEven (!ua.sign) (Y - rem) q
    else if rem = 0 then
      (fmt.pack ua.sign 0 0, {})
    else
      fmt.roundPack spec .roundTiesToEven ua.sign rem q
-- ANCHOR_END: remainder

end Format

end SoftFloat
