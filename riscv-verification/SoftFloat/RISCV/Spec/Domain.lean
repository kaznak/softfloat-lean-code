/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Format
import SoftFloat.RISCV.Base.Ops

namespace SoftFloat.RISCV.Spec

open SoftFloat

-- ANCHOR: Domain
def InstructionDomain.FCVTMOD_W_D (fmt : Format) (_a : BitVec fmt.width) : Prop := fmt = .binary64
-- ANCHOR_END: Domain

end SoftFloat.RISCV.Spec
