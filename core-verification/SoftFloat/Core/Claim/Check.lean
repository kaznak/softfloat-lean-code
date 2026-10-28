/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import Lean

namespace SoftFloat.Claim

open Lean Elab Command Meta

-- ANCHOR: ClaimStatementCheck
def claimPropositions (pfx mod : Name) : CommandElabM (List (Name × ConstantInfo)) := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? mod | throwError "the module {mod} is not imported"
  let named := env.constants.fold (init := []) fun acc n info =>
    if (pfx.isPrefixOf n || env.getModuleIdxFor? n == some modIdx) && !n.isInternal then (n, info) :: acc
    else acc
  liftTermElabM <| named.filterM fun (_, info) => isProp info.type

def checkClaimStatements (pfx mod : Name) (allowed : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let claims ← claimPropositions pfx mod
  if claims.isEmpty then throwError "no proposition of {pfx} or {mod} is found"
  for (c, info) in claims do
    for d in info.type.getUsedConstants do
      let some idx := env.getModuleIdxFor? d
        | throwError "the statement of {c} uses {d}, which is not from a module of {allowed}"
      let m := env.header.moduleNames[idx.toNat]!
      unless allowed.any (·.isPrefixOf m) do
        throwError "the statement of {c} uses {d} from {m}, which is not a module of {allowed}"
-- ANCHOR_END: ClaimStatementCheck

-- ANCHOR: ClaimAxiomCheck
def checkClaimAxioms (pfx mod : Name) : CommandElabM Unit := do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let claims ← claimPropositions pfx mod
  if claims.isEmpty then throwError "no proposition of {pfx} or {mod} is found"
  for (c, _) in claims do
    for a in ← collectAxioms c do
      unless allowed.contains a do
        throwError "{c} depends on the axiom {a}"
-- ANCHOR_END: ClaimAxiomCheck

end SoftFloat.Claim
