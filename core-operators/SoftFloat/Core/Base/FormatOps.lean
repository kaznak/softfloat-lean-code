/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Base.Format
import SoftFloat.Core.Base.Class

namespace SoftFloat

-- ANCHOR: FormatOps
structure FormatOps (fmt : Format) where
  addition : RoundingDirection → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  subtraction : RoundingDirection → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  multiplication : RoundingDirection → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  division : RoundingDirection → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  squareRoot : RoundingDirection → BitVec fmt.width → BitVec fmt.width × StatusFlags
  fusedMultiplyAdd : RoundingDirection → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width →
    BitVec fmt.width × StatusFlags
  roundToIntegral : RoundingDirection → (exact : Bool) → BitVec fmt.width → BitVec fmt.width × StatusFlags
  compareQuietEqual : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  compareSignalingEqual : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  compareSignalingLess : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  compareQuietLess : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  compareSignalingLessEqual : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  compareQuietLessEqual : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  convertFormat : RoundingDirection → (dst : Format) → BitVec fmt.width → BitVec dst.width × StatusFlags
  convertToInteger : RoundingDirection → (exact signed : Bool) → (w : Nat) → BitVec fmt.width →
    BitVec w × StatusFlags
  convertFromInt : RoundingDirection → (signed : Bool) → {w : Nat} → BitVec w → BitVec fmt.width × StatusFlags
  copy : BitVec fmt.width → BitVec fmt.width
  abs : BitVec fmt.width → BitVec fmt.width
  negate : BitVec fmt.width → BitVec fmt.width
  copySign : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width
  classOf : BitVec fmt.width → Class
  minimumNumber : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  maximumNumber : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  minimum : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  maximum : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
-- ANCHOR_END: FormatOps

end SoftFloat
