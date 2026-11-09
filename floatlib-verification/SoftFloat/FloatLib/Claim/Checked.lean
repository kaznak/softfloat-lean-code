/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Claim
import SoftFloat.Core.Claim.Check

namespace SoftFloat.FloatLib.Claim

open Lean Elab Command
open SoftFloat.Claim

-- ANCHOR: FloatLibClaimChecks
def claimChecks : CommandElabM Unit := do
  checkClaimStatements `SoftFloat.FloatLib.Claim `SoftFloat.FloatLib.Claim
    [`SoftFloat.Core.Base, `SoftFloat.Core.Operators, `SoftFloat.Core.Spec,
      `SoftFloat.FloatLib.Operators, `SoftFloat.FloatLib.Spec, `Init]
  checkClaimAxioms `SoftFloat.FloatLib.Claim `SoftFloat.FloatLib.Claim

run_cmd claimChecks
-- ANCHOR_END: FloatLibClaimChecks

end SoftFloat.FloatLib.Claim
