/-
Prints the modules each module imports, as built: one line for each import,
the name of the module and the name of the module it imports, separated by a
tab. scripts/check-package-dependencies.sh reads it to judge the directions of
the layers.

    lean --run scripts/module-imports.lean MODULES

MODULES is a file with one module a line: its name and the path of its .olean,
separated by a tab. The imports are read from the .olean, the environment as
Lean built it, not from the text of the source. The .olean files are read as
they are, without a search path: the packages of this repository put their
modules under the same head SoftFloat, which the search path of Lean cannot
tell apart.
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let [modulesFile] := args
    | IO.eprintln "usage: module-imports.lean MODULES"; return 1
  for line in ← IO.FS.lines modulesFile do
    match line.splitOn "\t" with
    | [mod, olean] =>
      let (data, _) ← readModuleData olean
      for i in data.imports do
        IO.println s!"{mod}\t{i.module}"
    | _ => if line != "" then IO.eprintln s!"not a module and a path: {line}"; return 1
  return 0
