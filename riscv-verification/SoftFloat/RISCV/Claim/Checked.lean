/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.RISCV.Claim
import SoftFloat.Core.Claim.Check

namespace SoftFloat.RISCV.Claim

open Lean Elab Command
open SoftFloat.Claim

-- ANCHOR: RiscvClaimChecks
def claimChecks : CommandElabM Unit := do
  checkClaimStatements `SoftFloat.RISCV.Claim `SoftFloat.RISCV.Claim
    [`SoftFloat.Core.Base, `SoftFloat.Core.Operators, `SoftFloat.Core.Spec,
      `SoftFloat.RISCV.Base, `SoftFloat.RISCV.Operators, `SoftFloat.RISCV.Spec, `Init]
  checkClaimAxioms `SoftFloat.RISCV.Claim `SoftFloat.RISCV.Claim

run_cmd claimChecks
-- ANCHOR_END: RiscvClaimChecks

end SoftFloat.RISCV.Claim
