/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Format
import SoftFloat.Core.Base.Types

namespace SoftFloat

-- ANCHOR: Tininess
inductive Tininess where
  | beforeRounding
  | afterRounding
  deriving DecidableEq, Repr
-- ANCHOR_END: Tininess

-- ANCHOR: Specialization
inductive NaNOperation where
  | addition
  | subtraction
  | multiplication
  | division
  | squareRoot
  | fusedMultiplyAdd
  | convertFormat
  | roundToIntegral (rm : RoundingDirection) (exact : Bool)
  | minimumNumber
  | maximumNumber
  | minimum
  | maximum
  | nextUp
  | nextDown
  | minNum
  | maxNum
  | minNumMag
  | maxNumMag
  | minimumMagnitude
  | minimumMagnitudeNumber
  | maximumMagnitude
  | maximumMagnitudeNumber
  | remainder
  | logB
  | scaleB
  deriving DecidableEq, Repr

inductive MinNumMaxNumOperation where
  | minNum
  | maxNum
  | minNumMag
  | maxNumMag
  deriving DecidableEq, Repr

structure Specialization where
  propagateNaN : NaNOperation → (dst : Format) → List (Format × Nat) → Nat
  setPayloadSign : (signaling : Bool) → (dst : Format) → (payload : Nat) → Bool
  fusedMultiplyAddZeroInfinityQuietNaNInvalid : Bool
  tininess : Tininess
  intOutOfRange : (src : Format) → RoundingDirection → (exact : Bool) → (signed : Bool) → (w : Nat) → (x : Nat) → Nat
  totalOrderNaN : (fmt : Format) → (x y : Nat) → Bool
  admissiblePayload : (signaling : Bool) → (fmt : Format) → (payload : Nat) → Bool
  minNumMaxNumOfEqual : MinNumMaxNumOperation → (fmt : Format) → (x y : Nat) → Nat
  scaleBOfNaNExponent : (fmt : Format) → RoundingDirection → (x n : Nat) → Nat × StatusFlags
-- ANCHOR_END: Specialization

end SoftFloat
