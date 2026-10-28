/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Spec.Agree
import SoftFloat.RISCV.Spec.Domain
import SoftFloat.Core.Spec.Coverage

namespace SoftFloat.RISCV.Spec

open Lean Elab Command Meta

-- ANCHOR: Coverage
def checkAssumesDomain (s dom f : Name) : MetaM Unit := do
  let env ← getEnv
  let some info := env.find? (s ++ f) | throwError "{s}.{f} is not found"
  let some (.inductInfo ind) := env.find? s | throwError "{s} is not found"
  forallTelescope info.type fun xs _ => do
    let k := ind.numParams + 1
    let binders := xs.extract k xs.size
    let mut fmts := #[]
    for p in xs.extract 0 ind.numParams do
      if (← inferType p) == mkConst ``SoftFloat.Format then fmts := fmts.push p
    let mut hyps := #[]
    let mut data := #[]
    for x in binders do
      if ← isProp (← inferType x) then hyps := hyps.push x else data := data.push x
    if env.contains (dom ++ f) then
      let ok ← match hyps.toList with
        | [h] => pure (binders.back? == some h &&
            (← inferType h) == mkAppN (.const (dom ++ f) []) (fmts ++ data))
        | _ => pure false
      unless ok do
        throwError "{s}.{f} does not assume exactly {dom}.{f} of its arguments"
    else unless hyps.isEmpty do
      throwError "{s}.{f} assumes something, but {dom}.{f} is not found"

def checkCoverageOf (ops correct agree dom : Name) : CommandElabM Unit := do
  let env ← getEnv
  let fs := getStructureFields env ops
  if fs.isEmpty then throwError "{ops} has no field"
  for s in [correct, agree] do
    let gs := getStructureFields env s
    unless fs == gs do
      throwError "the fields of {ops} and {s} differ:\n  {ops}: {fs}\n  {s}: {gs}"
  for f in fs do
    let some info := env.find? (correct ++ f) | throwError "{correct}.{f} is not found"
    let used := info.type.getUsedConstants
    unless used.contains (ops ++ f) do
      throwError "{correct}.{f} does not state anything about {ops}.{f}"
    for g in fs do
      if g != f && used.contains (ops ++ g) then
        throwError "{correct}.{f} states something about {ops}.{g}"
    for s in [correct, agree] do
      liftTermElabM (checkAssumesDomain s dom f)
    liftTermElabM (SoftFloat.Spec.checkAgreeStatesEquality ops agree f none true)
  let doms := env.constants.fold (init := #[]) fun acc n _ =>
    if dom.isPrefixOf n && n != dom && !n.isInternal then acc.push n else acc
  for d in doms do
    unless fs.any (fun f => dom ++ f == d) do
      throwError "{d} is not the precondition of a field of {ops}"

def checkCoverage : CommandElabM Unit := do
  checkCoverageOf ``SoftFloat.RISCV.InstructionOps ``InstructionCorrect ``InstructionAgree
    `SoftFloat.RISCV.Spec.InstructionDomain
  checkCoverageOf ``SoftFloat.RISCV.ConversionOps ``ConversionCorrect ``ConversionAgree
    `SoftFloat.RISCV.Spec.ConversionDomain
  checkCoverageOf ``SoftFloat.RISCV.WideningOps ``WideningCorrect ``WideningAgree
    `SoftFloat.RISCV.Spec.WideningDomain
  checkCoverageOf ``SoftFloat.RISCV.VectorOps ``VectorCorrect ``VectorAgree
    `SoftFloat.RISCV.Spec.VectorDomain

run_cmd checkCoverage
-- ANCHOR_END: Coverage

-- ANCHOR: RiscvCoverage
def checkSameBinders (correct agree f : Name) : MetaM Unit := do
  let env ← getEnv
  let some cInfo := env.find? (correct ++ f) | throwError "{correct}.{f} is not found"
  let some aInfo := env.find? (agree ++ f) | throwError "{agree}.{f} is not found"
  let some (.inductInfo cInd) := env.find? correct | throwError "{correct} is not found"
  let some (.inductInfo aInd) := env.find? agree | throwError "{agree} is not found"
  forallTelescope cInfo.type fun xs _ =>
  forallBoundedTelescope aInfo.type (some (aInd.numParams + 1)) fun _ rest => do
    let mut rest := rest
    for x in xs.extract (cInd.numParams + 1) xs.size do
      let .forallE _ t b _ := rest
        | throwError "{agree}.{f} quantifies over fewer arguments than {correct}.{f}"
      unless ← isDefEq t (← inferType x) do
        throwError "{agree}.{f} quantifies over other arguments than {correct}.{f}"
      rest := b.instantiate1 x
    if rest.isForall then
      throwError "{agree}.{f} quantifies over more arguments than {correct}.{f}"

def checkOperationsCoverage (ops correct agree : Name) (groups : List (Name × Name × Option Name)) :
    CommandElabM Unit := do
  let env ← getEnv
  let fs := getStructureFields env ops
  if fs.isEmpty then throwError "{ops} has no field"
  let cs := getStructureFields env correct
  unless cs.extract 0 fs.size == fs do
    throwError "the fields of {ops} are not the first fields of {correct}:\n  {ops}: {fs}\n  {correct}: {cs}"
  let mut functions := #[]
  for f in fs do
    let some info := env.find? (ops ++ f) | throwError "{ops}.{f} is not found"
    let ft := info.type.bindingBody!
    if ft.isForall then functions := functions.push f
    let used := fun (s : Name) => do
      let some i := env.find? (s ++ f) | throwError "{s}.{f} is not found"
      let u := i.type.getUsedConstants
      unless u.contains (ops ++ f) do
        throwError "{s}.{f} does not state anything about {ops}.{f}"
      for g in fs do
        if g != f && u.contains (ops ++ g) then
          throwError "{s}.{f} states something about {ops}.{g}"
      pure u
    let cu ← used correct
    let au ← if ft.isForall then used agree else pure #[]
    let mut wrap := none
    if let .const t _ := ft.getForallBody.getAppFn then
      if isStructure env t then
        let some (_, c, a) := groups.find? (·.1 == t)
          | throwError "{ops}.{f} gives a value of {t}, which has no predicate of correctness"
        unless cu.contains c do
          throwError "{correct}.{f} does not state {c} of {ops}.{f}"
        if let some a := a then
          if ft.isForall && !au.contains a then
            throwError "{agree}.{f} does not state {a} of {ops}.{f}"
        wrap := a
    if ft.isForall then
      liftTermElabM (checkSameBinders correct agree f)
      liftTermElabM (SoftFloat.Spec.checkAgreeStatesEquality ops agree f wrap false)
  let as := getStructureFields env agree
  unless as == functions do
    throwError "the fields of {agree} are not the fields of {ops} that are functions:\n  {agree}: {as}\n  functions: {functions}"

run_cmd (checkOperationsCoverage ``SoftFloat.RISCV.RiscvOps ``RiscvCorrect ``RiscvAgree
  [(``SoftFloat.RISCV.InstructionOps, ``InstructionCorrect, some ``InstructionAgree),
    (``SoftFloat.RISCV.ConversionOps, ``ConversionCorrect, some ``ConversionAgree),
    (``SoftFloat.RISCV.WideningOps, ``WideningCorrect, some ``WideningAgree),
    (``SoftFloat.RISCV.VectorOps, ``VectorCorrect, some ``VectorAgree),
    (``SoftFloat.FormatOps, ``SoftFloat.Spec.FormatCorrect, none)])
-- ANCHOR_END: RiscvCoverage

end SoftFloat.RISCV.Spec
