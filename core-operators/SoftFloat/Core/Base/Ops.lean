/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Base.Format
import SoftFloat.Core.Base.Class
import SoftFloat.Core.Base.LogBFormat

namespace SoftFloat

-- ANCHOR: Ops
structure Ops where
  addition : (fa fb dst : Format) → RoundingDirection → Nat → Nat → Nat × StatusFlags
  subtraction : (fa fb dst : Format) → RoundingDirection → Nat → Nat → Nat × StatusFlags
  multiplication : (fa fb dst : Format) → RoundingDirection → Nat → Nat → Nat × StatusFlags
  division : (fa fb dst : Format) → RoundingDirection → Nat → Nat → Nat × StatusFlags
  squareRoot : (fa dst : Format) → RoundingDirection → Nat → Nat × StatusFlags
  fusedMultiplyAdd : (fa fb fc dst : Format) → RoundingDirection → Nat → Nat → Nat → Nat × StatusFlags
  convertFormat : (src dst : Format) → RoundingDirection → Nat → Nat × StatusFlags
  convertFromInt : Format → RoundingDirection → Int → Nat × StatusFlags
  convertToInteger : Format → RoundingDirection → (exact signed : Bool) → (w : Nat) → Nat → Nat × StatusFlags
  roundToIntegral : Format → RoundingDirection → (exact : Bool) → Nat → Nat × StatusFlags
  comparison : (fa fb : Format) → (signaling : Bool) → (holds : Relation → Bool) → Nat → Nat → Bool × StatusFlags
  copy : Format → Nat → Nat
  negate : Format → Nat → Nat
  abs : Format → Nat → Nat
  copySign : Format → Nat → Nat → Nat
  minimumNumber : Format → Nat → Nat → Nat × StatusFlags
  maximumNumber : Format → Nat → Nat → Nat × StatusFlags
  minimum : Format → Nat → Nat → Nat × StatusFlags
  maximum : Format → Nat → Nat → Nat × StatusFlags
  classOf : Format → Nat → Class
  isSignMinus : Format → Nat → Bool
  isNormal : Format → Nat → Bool
  isFinite : Format → Nat → Bool
  isZero : Format → Nat → Bool
  isSubnormal : Format → Nat → Bool
  isInfinite : Format → Nat → Bool
  isNaN : Format → Nat → Bool
  isSignaling : Format → Nat → Bool
  isCanonical : Format → Nat → Bool
  radix : Format → Nat → Nat
  totalOrder : Format → Nat → Nat → Bool
  totalOrderMag : Format → Nat → Nat → Bool
  nextUp : Format → Nat → Nat × StatusFlags
  nextDown : Format → Nat → Nat × StatusFlags
  minNum : Format → Nat → Nat → Nat × StatusFlags
  maxNum : Format → Nat → Nat → Nat × StatusFlags
  minNumMag : Format → Nat → Nat → Nat × StatusFlags
  maxNumMag : Format → Nat → Nat → Nat × StatusFlags
  minimumMagnitude : Format → Nat → Nat → Nat × StatusFlags
  minimumMagnitudeNumber : Format → Nat → Nat → Nat × StatusFlags
  maximumMagnitude : Format → Nat → Nat → Nat × StatusFlags
  maximumMagnitudeNumber : Format → Nat → Nat → Nat × StatusFlags
  remainder : Format → Nat → Nat → Nat × StatusFlags
  getPayload : Format → Nat → Nat × StatusFlags
  setPayload : Format → Nat → Nat × StatusFlags
  setPayloadSignaling : Format → Nat → Nat × StatusFlags
  logB : (fmt : Format) → LogBFormat → Nat → Nat × StatusFlags
  scaleB : (fmt : Format) → LogBFormat → RoundingDirection → Nat → Nat → Nat × StatusFlags
-- ANCHOR_END: Ops

end SoftFloat
