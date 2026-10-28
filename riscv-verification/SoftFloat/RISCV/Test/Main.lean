/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import Lean
import SoftFloat.RISCV.Operators

namespace SoftFloat.RISCV.Test

open SoftFloat SoftFloat.RISCV

-- ANCHOR: OperationTable
inductive Rounding where
  | mode (rm : RoundingMode)
  | odd

def roundings : List (String × Rounding) :=
  [("near_even", .mode .RNE), ("minMag", .mode .RTZ), ("min", .mode .RDN), ("max", .mode .RUP),
   ("near_maxMag", .mode .RMM), ("odd", .odd)]

def parseRM (name : String) : Option Rounding :=
  roundings.lookup name

inductive Op where
  | binary (f : Nat → Nat → Nat × StatusFlags)
  | unary (f : Nat → Nat × StatusFlags)
  | ternary (f : Nat → Nat → Nat → Nat × StatusFlags)

def binary {w : Nat} (f : BitVec w → BitVec w → BitVec w × StatusFlags) : Op :=
  .binary fun a b => let (r, fl) := f (.ofNat w a) (.ofNat w b); (r.toNat, fl)

def unary {w v : Nat} (f : BitVec w → BitVec v × StatusFlags) : Op :=
  .unary fun a => let (r, fl) := f (.ofNat w a); (r.toNat, fl)

def ternary {w : Nat} (f : BitVec w → BitVec w → BitVec w → BitVec w × StatusFlags) : Op :=
  .ternary fun a b c =>
    let (r, fl) := f (.ofNat w a) (.ofNat w b) (.ofNat w c); (r.toNat, fl)

def compare {w : Nat} (f : BitVec w → BitVec w → Bool × StatusFlags) : Op :=
  .binary fun a b => let (r, fl) := f (.ofNat w a) (.ofNat w b); (if r then 1 else 0, fl)

open Lean Meta in
partial def declPath (e : Expr) : MetaM Name := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFn.consumeMData with
  | .const c _ =>
    match ← getProjectionFnInfo? c with
    | some info =>
      let some s := e.getAppArgs[info.numParams]?
        | throwError "the field {c} is not applied to a value: {e}"
      return .str (← declPath s) c.getString!
    | none => return c
  | .fvar x =>
    match ← x.getValue? with
    | some v => declPath (mkAppN v e.getAppArgs)
    | none => throwError "a variable names no declaration: {e}"
  | _ => throwError "names no declaration: {e}"

syntax (name := declOf) "declOf% " term:max : term

open Lean Elab Term in
@[term_elab declOf]
def elabDeclOf : TermElab := fun stx _ => do
  let e ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  return toExpr (← declPath e)

structure Entry where
  decl : Lean.Name
  op : Op

syntax (name := entry) "entry% " ident term:max : term

macro_rules (kind := entry)
  | `(entry% $wrap $f) => `(({ decl := declOf% $f, op := $wrap $f } : Entry))

structure TestFloatOps where
  name : String
  add : Option Entry := none
  sub : Option Entry := none
  mul : Option Entry := none
  div : Option Entry := none
  sqrt : Option Entry := none
  mulAdd : Option Entry := none
  roundToInt : Option Entry := none
  roundToIntNotExact : Option Entry := none
  eq : Option Entry := none
  eqSignaling : Option Entry := none
  lt : Option Entry := none
  ltQuiet : Option Entry := none
  le : Option Entry := none
  leQuiet : Option Entry := none
  toI32 : Option Entry := none
  toUI32 : Option Entry := none
  toI64 : Option Entry := none
  toUI64 : Option Entry := none
  fromI32 : Option Entry := none
  fromUI32 : Option Entry := none
  fromI64 : Option Entry := none
  fromUI64 : Option Entry := none

def TestFloatOps.ops (f : TestFloatOps) : List (String × Entry) :=
  let named : List (String × Option Entry) :=
    [("add", f.add), ("sub", f.sub), ("mul", f.mul), ("div", f.div), ("sqrt", f.sqrt),
     ("mulAdd", f.mulAdd), ("roundToInt", f.roundToInt), ("roundToInt_notexact", f.roundToIntNotExact),
     ("eq", f.eq), ("eq_signaling", f.eqSignaling), ("lt", f.lt), ("lt_quiet", f.ltQuiet),
     ("le", f.le), ("le_quiet", f.leQuiet),
     ("to_i32", f.toI32), ("to_ui32", f.toUI32), ("to_i64", f.toI64), ("to_ui64", f.toUI64)
    ].map (fun (op, o) => (s!"{f.name}_{op}", o)) ++
    [("i32", f.fromI32), ("ui32", f.fromUI32), ("i64", f.fromI64), ("ui64", f.fromUI64)
    ].map (fun (int, o) => (s!"{int}_to_{f.name}", o))
  named.filterMap fun (name, o) => o.map (name, ·)

syntax (name := ofFormat) "ofFormat% " str term:max term:max : term

macro_rules (kind := ofFormat)
  | `(ofFormat% $name $fmt $fo) => `(fun (r : Rounding) => match r with
    | .mode rm =>
      ({ name := $name
         add := entry% binary ((riscv.instructions $fmt).FADD rm)
         sub := entry% binary ((riscv.instructions $fmt).FSUB rm)
         mul := entry% binary ((riscv.instructions $fmt).FMUL rm)
         div := entry% binary ((riscv.instructions $fmt).FDIV rm)
         sqrt := entry% unary ((riscv.instructions $fmt).FSQRT rm)
         mulAdd := entry% ternary ((riscv.instructions $fmt).FMADD rm)
         roundToInt := entry% unary ((riscv.instructions $fmt).FROUNDNX rm)
         roundToIntNotExact := entry% unary ((riscv.instructions $fmt).FROUND rm)
         eq := entry% compare (riscv.instructions $fmt).FEQ
         eqSignaling := entry% compare ($fo).compareSignalingEqual
         lt := entry% compare (riscv.instructions $fmt).FLT
         ltQuiet := entry% compare (riscv.instructions $fmt).FLTQ
         le := entry% compare (riscv.instructions $fmt).FLE
         leQuiet := entry% compare (riscv.instructions $fmt).FLEQ
         toI32 := entry% unary ((riscv.instructions $fmt).FCVT_W_F rm)
         toUI32 := entry% unary ((riscv.instructions $fmt).FCVT_WU_F rm)
         toI64 := entry% unary ((riscv.instructions $fmt).FCVT_L_F rm)
         toUI64 := entry% unary ((riscv.instructions $fmt).FCVT_LU_F rm)
         fromI32 := entry% unary ((riscv.instructions $fmt).FCVT_F_W rm)
         fromUI32 := entry% unary ((riscv.instructions $fmt).FCVT_F_WU rm)
         fromI64 := entry% unary ((riscv.instructions $fmt).FCVT_F_L rm)
         fromUI64 := entry% unary ((riscv.instructions $fmt).FCVT_F_LU rm) } : TestFloatOps)
    | .odd =>
      ({ name := $name
         add := entry% binary (($fo).addition .roundToOdd)
         sub := entry% binary (($fo).subtraction .roundToOdd)
         mul := entry% binary (($fo).multiplication .roundToOdd)
         div := entry% binary (($fo).division .roundToOdd)
         sqrt := entry% unary (($fo).squareRoot .roundToOdd)
         mulAdd := entry% ternary (($fo).fusedMultiplyAdd .roundToOdd)
         roundToInt := entry% unary (($fo).roundToIntegral .roundToOdd true)
         roundToIntNotExact := entry% unary (($fo).roundToIntegral .roundToOdd false)
         eq := entry% compare (riscv.instructions $fmt).FEQ
         eqSignaling := entry% compare ($fo).compareSignalingEqual
         lt := entry% compare (riscv.instructions $fmt).FLT
         ltQuiet := entry% compare (riscv.instructions $fmt).FLTQ
         le := entry% compare (riscv.instructions $fmt).FLE
         leQuiet := entry% compare (riscv.instructions $fmt).FLEQ
         toI32 := entry% unary (($fo).convertToInteger .roundToOdd true true 32)
         toUI32 := entry% unary (($fo).convertToInteger .roundToOdd true false 32)
         toI64 := entry% unary (($fo).convertToInteger .roundToOdd true true 64)
         toUI64 := entry% unary (($fo).convertToInteger .roundToOdd true false 64)
         fromI32 := entry% unary (($fo).convertFromInt .roundToOdd true (w := 32))
         fromUI32 := entry% unary (($fo).convertFromInt .roundToOdd false (w := 32))
         fromI64 := entry% unary (($fo).convertFromInt .roundToOdd true (w := 64))
         fromUI64 := entry% unary (($fo).convertFromInt .roundToOdd false (w := 64)) } : TestFloatOps))

def f16 : Rounding → TestFloatOps := ofFormat% "f16" .binary16 riscv.F16

def f32 : Rounding → TestFloatOps := ofFormat% "f32" .binary32 riscv.F32

def f64 : Rounding → TestFloatOps := ofFormat% "f64" .binary64 riscv.F64

def f128 : Rounding → TestFloatOps := ofFormat% "f128" .binary128 riscv.F128

def formatConversions : Rounding → List (String × Entry)
  | .mode rm => [
    ("f16_to_f32", entry% unary ((riscv.conversions .binary16 .binary32).FCVT rm)),
    ("f16_to_f64", entry% unary ((riscv.conversions .binary16 .binary64).FCVT rm)),
    ("f32_to_f64", entry% unary ((riscv.conversions .binary32 .binary64).FCVT rm)),
    ("f32_to_f16", entry% unary ((riscv.conversions .binary32 .binary16).FCVT rm)),
    ("f64_to_f16", entry% unary ((riscv.conversions .binary64 .binary16).FCVT rm)),
    ("f64_to_f32", entry% unary ((riscv.conversions .binary64 .binary32).FCVT rm)),
    ("f16_to_f128", entry% unary ((riscv.conversions .binary16 .binary128).FCVT rm)),
    ("f32_to_f128", entry% unary ((riscv.conversions .binary32 .binary128).FCVT rm)),
    ("f64_to_f128", entry% unary ((riscv.conversions .binary64 .binary128).FCVT rm)),
    ("f128_to_f16", entry% unary ((riscv.conversions .binary128 .binary16).FCVT rm)),
    ("f128_to_f32", entry% unary ((riscv.conversions .binary128 .binary32).FCVT rm)),
    ("f128_to_f64", entry% unary ((riscv.conversions .binary128 .binary64).FCVT rm)),
    ("f32_to_bf16", entry% unary ((riscv.conversions .binary32 .bf16).FCVT rm)),
    ("bf16_to_f32", entry% unary ((riscv.conversions .bf16 .binary32).FCVT rm)),
  ]
  | .odd => [
    ("f16_to_f32", entry% unary (riscv.F16.convertFormat .roundToOdd .binary32)),
    ("f16_to_f64", entry% unary (riscv.F16.convertFormat .roundToOdd .binary64)),
    ("f32_to_f64", entry% unary (riscv.F32.convertFormat .roundToOdd .binary64)),
    ("f32_to_f16", entry% unary (riscv.widenings .binary16 .binary32).VFNCVT_ROD_F_F_W),
    ("f64_to_f16", entry% unary (riscv.F64.convertFormat .roundToOdd .binary16)),
    ("f64_to_f32", entry% unary (riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W),
    ("f16_to_f128", entry% unary (riscv.F16.convertFormat .roundToOdd .binary128)),
    ("f32_to_f128", entry% unary (riscv.F32.convertFormat .roundToOdd .binary128)),
    ("f64_to_f128", entry% unary (riscv.F64.convertFormat .roundToOdd .binary128)),
    ("f128_to_f16", entry% unary (riscv.F128.convertFormat .roundToOdd .binary16)),
    ("f128_to_f32", entry% unary (riscv.F128.convertFormat .roundToOdd .binary32)),
    ("f128_to_f64", entry% unary (riscv.F128.convertFormat .roundToOdd .binary64)),
    ("f32_to_bf16", entry% unary (riscv.F32.convertFormat .roundToOdd .bf16)),
  ]

def testFloatOps (r : Rounding) : List (String × Entry) :=
  [f16 r, f32 r, f64 r, f128 r].flatMap TestFloatOps.ops ++ formatConversions r

def opTable (r : Rounding) (name : String) : Option Op :=
  ((testFloatOps r).lookup name).map (·.op)
-- ANCHOR_END: OperationTable

def parseHex (s : String) : Option Nat :=
  s.foldl (init := some 0) fun acc c => do
    let n ← acc
    let d ←
      if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else none
    pure (n * 16 + d)

def hexN (digits : Nat) (n : Nat) : String :=
  let s := (String.ofList (Nat.toDigits 16 n)).toUpper
  "".pushn '0' (digits - s.length) ++ s

def hex32 (n : Nat) : String := hexN 8 n

def hex64 (n : Nat) : String := hexN 16 n

def digitsOfTok (t : String) : Nat :=
  if t.endsWith "128" then 32 else if t.endsWith "64" then 16 else if t.endsWith "16" then 4 else 8

def hexDigitsOf (opName : String) : Nat × Nat :=
  let toks := opName.splitOn "_"
  let dIn := digitsOfTok (toks.headD "f32")
  let dOut :=
    if toks.contains "to" then digitsOfTok (toks.getLastD "f32")
    else if toks.contains "eq" || toks.contains "lt" || toks.contains "le" then 1
    else dIn
  (dIn, dOut)

end SoftFloat.RISCV.Test

-- ANCHOR: Main
open SoftFloat SoftFloat.RISCV SoftFloat.RISCV.Test in
def main (args : List String) : IO UInt32 := do
  if args == ["--list"] then
    for (rmName, r) in roundings do
      for (name, e) in testFloatOps r do
        IO.println s!"{rmName} {name} {e.decl}"
    return 0
  let [opName, rmName, path] := args
    | do IO.eprintln "usage: testfloat_check <op> <near_even|minMag|min|max|near_maxMag|odd> <vector-file>\n       testfloat_check --list"
         return 2
  let some rm := parseRM rmName | do IO.eprintln s!"unknown rounding mode: {rmName}"; return 2
  let some op := opTable rm opName | do IO.eprintln s!"unknown op: {opName}"; return 2
  let (dIn, dOut) := hexDigitsOf opName
  let hex : Nat → String := hexN dIn
  let hexOut : Nat → String := hexN dOut

  let h ← IO.FS.Handle.mk path .read
  let mut total := 0
  let mut resBad := 0
  let mut flagBad := 0
  let mut parseBad := 0
  let mut done := false

  while !done do
    let line ← h.getLine
    if line.isEmpty then
      done := true
    else
      let toks := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
      let parsed : Option (String × Nat × Nat × Nat × StatusFlags) :=
        match op, toks with
        | .binary f, [aS, bS, rS, flS] =>
          match parseHex aS, parseHex bS, parseHex rS, parseHex flS with
          | some a, some b, some rExp, some flExp =>
            let (rGot, flGot) := f a b
            some (s!"A={hex a} B={hex b}", rExp, flExp, rGot, flGot)
          | _, _, _, _ => none
        | .unary f, [aS, rS, flS] =>
          match parseHex aS, parseHex rS, parseHex flS with
          | some a, some rExp, some flExp =>
            let (rGot, flGot) := f a
            some (s!"A={hex a}", rExp, flExp, rGot, flGot)
          | _, _, _ => none
        | .ternary f, [aS, bS, cS, rS, flS] =>
          match parseHex aS, parseHex bS, parseHex cS, parseHex rS, parseHex flS with
          | some a, some b, some c, some rExp, some flExp =>
            let (rGot, flGot) := f a b c
            some (s!"A={hex a} B={hex b} C={hex c}", rExp, flExp, rGot, flGot)
          | _, _, _, _, _ => none
        | _, [] => none
        | _, _ => none
      match parsed with
      | some (inS, rExp, flExp, rGot, flGot) =>
        total := total + 1
        if rGot ≠ rExp then
          resBad := resBad + 1
          if resBad ≤ 20 then
            IO.println s!"MISMATCH {opName}: {inS} expected={hexOut rExp} got={hexOut rGot} (flags exp={flExp} got={riscv.toFflags flGot})"
        if riscv.toFflags flGot ≠ flExp then
          flagBad := flagBad + 1
          if flagBad ≤ 20 then
            IO.println s!"FLAG MISMATCH {opName}: {inS} result={hexOut rGot} flags expected={flExp} got={riscv.toFflags flGot}"
        if total % 1000000 == 0 then
          IO.println s!"... {total} vectors processed (result mismatches so far: {resBad})"
      | none =>
        if !toks.isEmpty then
          parseBad := parseBad + 1

  IO.println s!"{opName} -r{rmName}: total={total} result_mismatch={resBad} flag_mismatch={flagBad} parse_error={parseBad}"
  if resBad == 0 && flagBad == 0 && parseBad == 0 && total > 0 then
    IO.println "GREEN (result bits and exception flags all match)"
    return 0
  else
    return 1
-- ANCHOR_END: Main
