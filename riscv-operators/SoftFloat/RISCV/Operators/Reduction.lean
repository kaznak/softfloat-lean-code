/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types

namespace SoftFloat.RISCV

-- ANCHOR: Reduction
def reduceWithFlags {α β : Type} (step : α → β → α × StatusFlags) : α → List β → α × StatusFlags
  | a, [] => (a, {})
  | a, x :: xs =>
    let s := step a x
    let t := reduceWithFlags step s.1 xs
    (t.1, s.2.union t.2)
-- ANCHOR_END: Reduction

end SoftFloat.RISCV
