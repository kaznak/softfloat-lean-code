/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
namespace SoftFloat

-- ANCHOR: LogBFormat
inductive LogBFormat where
  | sourceFormat
  | integer (w : Nat) (nanValue infinityValue zeroValue : Int)
  deriving DecidableEq, Repr
-- ANCHOR_END: LogBFormat

end SoftFloat
