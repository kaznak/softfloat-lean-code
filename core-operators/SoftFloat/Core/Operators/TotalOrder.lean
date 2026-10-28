/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Sign
import SoftFloat.Core.Operators.Compare

namespace SoftFloat

-- ANCHOR: TotalOrder
namespace Format

def totalOrder (spec : Specialization) (fmt : Format) (a b : Nat) : Bool :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if ua.sign != ub.sign then ua.sign
  else if fmt.isNaNU ua && fmt.isNaNU ub && fmt.isSNaNU ua == fmt.isSNaNU ub then spec.totalOrderNaN fmt a b
  else if ua.sign then decide (fmt.orderKeyU ub ≤ fmt.orderKeyU ua)
  else decide (fmt.orderKeyU ua ≤ fmt.orderKeyU ub)

def totalOrderMag (spec : Specialization) (fmt : Format) (a b : Nat) : Bool :=
  fmt.totalOrder spec (fmt.abs a) (fmt.abs b)

end Format
-- ANCHOR_END: TotalOrder

end SoftFloat
