/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Compare
import SoftFloat.Core.Operators.MinMax

namespace SoftFloat

-- ANCHOR: minmaxMagnitude
namespace Format

def magnitudeSelect (fmt : Format) (pickLess : Bool) (a b : Nat) (fallback : Nat × StatusFlags) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if fmt.isNaNU ua || fmt.isNaNU ub then fallback
  else if fmt.orderKeyU ua < fmt.orderKeyU ub then (if pickLess then a else b, {})
  else if fmt.orderKeyU ub < fmt.orderKeyU ua then (if pickLess then b else a, {})
  else fallback

def minimumMagnitude (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect true a b (fmt.minimumWith spec .minimumMagnitude a b)

def minimumMagnitudeNumber (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect true a b (fmt.minimumNumberWith spec .minimumMagnitudeNumber a b)

def maximumMagnitude (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect false a b (fmt.maximumWith spec .maximumMagnitude a b)

def maximumMagnitudeNumber (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect false a b (fmt.maximumNumberWith spec .maximumMagnitudeNumber a b)

end Format
-- ANCHOR_END: minmaxMagnitude

end SoftFloat
