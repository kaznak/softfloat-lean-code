/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Sign

namespace SoftFloat

-- ANCHOR: NextUpDown
namespace Format

def nextUp (spec : Specialization) (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  if fmt.isNaNU u then
    (spec.propagateNaN .nextUp fmt [(fmt, a)], { invalidOperation := fmt.isSNaNU u })
  else if fmt.isInfU u && !u.sign then (a, {})
  else if isZeroU u then (fmt.pack false 0 1, {})
  else if u.sign then (a - 1, {})
  else (a + 1, {})

def nextDown (spec : Specialization) (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  if fmt.isNaNU u then
    (spec.propagateNaN .nextDown fmt [(fmt, a)], { invalidOperation := fmt.isSNaNU u })
  else
    let r := fmt.nextUp spec (fmt.negate a)
    (fmt.negate r.1, r.2)

end Format
-- ANCHOR_END: NextUpDown

end SoftFloat
