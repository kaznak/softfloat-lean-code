/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types

namespace SoftFloat.RISCV

-- ANCHOR: RoundingMode
inductive RoundingMode where
  | RNE
  | RTZ
  | RDN
  | RUP
  | RMM
  deriving DecidableEq, Repr

def RoundingMode.toRoundingDirection : RoundingMode → RoundingDirection
  | .RNE => .roundTiesToEven
  | .RTZ => .roundTowardZero
  | .RDN => .roundTowardNegative
  | .RUP => .roundTowardPositive
  | .RMM => .roundTiesToAway
-- ANCHOR_END: RoundingMode

end SoftFloat.RISCV
