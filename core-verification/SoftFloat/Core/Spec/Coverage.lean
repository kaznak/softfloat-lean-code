/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Correct
import SoftFloat.Core.Spec.Agree
import SoftFloat.Core.Spec.FormatCorrect

namespace SoftFloat.Spec

open Lean Elab Command Meta

-- ANCHOR: Coverage
def checkAssumesDomain (s f : Name) : MetaM Unit := do
  let env ← getEnv
  let dom := `SoftFloat.Spec.Domain ++ f
  let some info := env.find? (s ++ f) | throwError "{s}.{f} is not found"
  let some domInfo := env.find? dom | throwError "Domain.{f} is not found"
  let some (.inductInfo ind) := env.find? s | throwError "{s} is not found"
  forallTelescope domInfo.type fun ds _ =>
  forallTelescope info.type fun xs _ => do
    let k := ind.numParams + 1
    let ok ← if xs.size == k + ds.size + 1 then do
        let h ← inferType xs[xs.size - 1]!
        pure (h == mkAppN (.const dom []) (xs.extract k (xs.size - 1)))
      else pure false
    unless ok do
      throwError "{s}.{f} does not assume exactly Domain.{f} of its arguments"

def checkAgreeStatesEquality (ops agree f : Name) (wrap : Option Name) (exact : Bool) : MetaM Unit := do
  let env ← getEnv
  let some info := env.find? (agree ++ f) | throwError "{agree}.{f} is not found"
  let some (.inductInfo ind) := env.find? agree | throwError "{agree} is not found"
  let np := ind.numParams
  unless np ≥ 2 do throwError "{agree} does not take the two sets as its last parameters"
  forallTelescope info.type fun xs body => do
    let pre := xs.extract 0 (np - 2)
    let o₁ := xs[np - 2]!
    let o₂ := xs[np - 1]!
    let mut data := #[]
    for x in xs.extract (np + 1) xs.size do
      unless ← isProp (← inferType x) do data := data.push x
    let fieldArgs := fun (e o : Expr) =>
      let args := e.getAppArgs
      if e.getAppFn.isConstOf (ops ++ f) && args.size > pre.size &&
          args.extract 0 pre.size == pre && args[pre.size]! == o then
        some (args.extract (pre.size + 1) args.size)
      else none
    let sides : Option (Expr × Expr × Array Expr) := match wrap with
      | some a =>
        let args := body.getAppArgs
        if body.getAppFn.isConstOf a && args.size ≥ 2 then
          some (args[args.size - 2]!, args[args.size - 1]!, args.extract 0 (args.size - 2))
        else none
      | none => body.eq?.map fun (_, l, r) => (l, r, #[])
    let ok := match sides with
      | some (l, r, outer) =>
        match fieldArgs l o₁, fieldArgs r o₂ with
        | some a₁, some a₂ =>
          a₁ == a₂ && (wrap.isNone || outer == a₁) &&
            !a₁.any (fun a => a.containsFVar o₁.fvarId! || a.containsFVar o₂.fvarId!) &&
            data.all (fun d => a₁.any (·.containsFVar d.fvarId!)) &&
            (!exact || a₁ == data)
        | _, _ => false
      | none => false
    unless ok do
      throwError "{agree}.{f} does not state that the values of {ops}.{f} of the two sets on the same arguments are {
        match wrap with | some a => m!"in {a}" | none => m!"equal"}"

def checkCoverage : CommandElabM Unit := do
  let env ← getEnv
  let ops := getStructureFields env ``Ops
  for s in [``Correct, ``Agree] do
    let fs := getStructureFields env s
    unless ops == fs do
      throwError "the fields of Ops and {s} differ:\n  Ops: {ops}\n  {s}: {fs}"
  for f in ops do
    unless env.contains (`SoftFloat.Spec.Domain ++ f) do
      throwError "Domain.{f} is not found for Ops.{f}"
  for f in ops do
    let some info := env.find? (``Correct ++ f) | throwError "Correct.{f} is not found"
    let used := info.type.getUsedConstants
    unless used.contains (``Ops ++ f) do
      throwError "Correct.{f} does not state anything about Ops.{f}"
    for g in ops do
      if g != f && used.contains (``Ops ++ g) then
        throwError "Correct.{f} states something about Ops.{g}"
    for s in [``Correct, ``Agree] do
      liftTermElabM (checkAssumesDomain s f)
    liftTermElabM (checkAgreeStatesEquality ``Ops ``Agree f none true)
  let fops := getStructureFields env ``FormatOps
  let fcs := getStructureFields env ``FormatCorrect
  unless fops == fcs do
    throwError "the fields of FormatOps and FormatCorrect differ:\n  FormatOps: {fops}\n  FormatCorrect: {fcs}"
  for f in fops do
    let some info := env.find? (``FormatCorrect ++ f) | throwError "FormatCorrect.{f} is not found"
    let used := info.type.getUsedConstants
    unless used.contains (``FormatOps ++ f) do
      throwError "FormatCorrect.{f} does not state anything about FormatOps.{f}"
    for g in fops do
      if g != f && used.contains (``FormatOps ++ g) then
        throwError "FormatCorrect.{f} states something about FormatOps.{g}"
  let some (.inductInfo nanOps) := env.find? ``SoftFloat.NaNOperation
    | throwError "NaNOperation is not found"
  for c in nanOps.ctors do
    unless ops.contains (Name.mkSimple c.getString!) do
      throwError "NaNOperation.{c.getString!} is not a field of Ops"

run_cmd checkCoverage
-- ANCHOR_END: Coverage

end SoftFloat.Spec
