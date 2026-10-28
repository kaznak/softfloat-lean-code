/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Format

-- ANCHOR: BF16
namespace SoftFloat

def Format.bf16 : Format := ⟨8, 8, by decide, by decide, by decide⟩

end SoftFloat
-- ANCHOR_END: BF16
