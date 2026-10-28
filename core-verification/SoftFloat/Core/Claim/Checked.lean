/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Claim
import SoftFloat.Core.Claim.Check

namespace SoftFloat.Claim

open Lean Elab Command

-- ANCHOR: ClaimChecks
def claimChecks : CommandElabM Unit := do
  checkClaimStatements `SoftFloat.Claim `SoftFloat.Core.Claim
    [`SoftFloat.Core.Base, `SoftFloat.Core.Operators, `SoftFloat.Core.Spec, `Init]
  checkClaimAxioms `SoftFloat.Claim `SoftFloat.Core.Claim

run_cmd claimChecks
-- ANCHOR_END: ClaimChecks

end SoftFloat.Claim
