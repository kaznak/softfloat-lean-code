/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: Predicates
namespace Format

protected def isSignMinus (fmt : Format) (n : Nat) : Bool :=
  (fmt.unpack n).sign

protected def isNormal (fmt : Format) (n : Nat) : Bool :=
  fmt.isNormalU (fmt.unpack n)

protected def isFinite (fmt : Format) (n : Nat) : Bool :=
  (fmt.unpack n).expField != fmt.expMax

protected def isZero (fmt : Format) (n : Nat) : Bool :=
  isZeroU (fmt.unpack n)

protected def isSubnormal (fmt : Format) (n : Nat) : Bool :=
  isSubnormalU (fmt.unpack n)

protected def isInfinite (fmt : Format) (n : Nat) : Bool :=
  fmt.isInfU (fmt.unpack n)

protected def isNaN (fmt : Format) (n : Nat) : Bool :=
  fmt.isNaNU (fmt.unpack n)

protected def isSignaling (fmt : Format) (n : Nat) : Bool :=
  fmt.isSNaNU (fmt.unpack n)

protected def isCanonical (_fmt : Format) (_n : Nat) : Bool :=
  true

protected def radix (_fmt : Format) (_n : Nat) : Nat :=
  2

end Format
-- ANCHOR_END: Predicates

end SoftFloat
