/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec

namespace SoftFloat.RISCV.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: RoundingModeSpec
def roundingModeEncoding : Nat → Option RoundingDirection
  | 0 => some .roundTiesToEven
  | 1 => some .roundTowardZero
  | 2 => some .roundTowardNegative
  | 3 => some .roundTowardPositive
  | 4 => some .roundTiesToAway
  | _ => none

def selectedRoundingDirection (rm frm : Nat) : Option RoundingDirection :=
  if rm = 7 then roundingModeEncoding frm else roundingModeEncoding rm
-- ANCHOR_END: RoundingModeSpec

-- ANCHOR: InstructionsSpec
def negated (fmt : Format) (x : Nat) : Nat :=
  withSign fmt x (!(fmt.unpack x).sign)

def classMaskBit : FloatClass → Nat
  | .infinity true => 0
  | .normal true => 1
  | .subnormal true => 2
  | .zero true => 3
  | .zero false => 4
  | .subnormal false => 5
  | .normal false => 6
  | .infinity false => 7
  | .signalingNaN => 8
  | .quietNaN => 9
-- ANCHOR_END: InstructionsSpec

end SoftFloat.RISCV.Spec
