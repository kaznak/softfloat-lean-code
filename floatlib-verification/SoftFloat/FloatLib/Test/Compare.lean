/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators
import SoftFloat.FloatLib.Operators.Specialization
import SoftFloat.FloatLib.Spec.Ops

/-!
# Comparisons with FloatLib on chosen inputs

The operations of SoftFloat with the specialization `floatlib` and the operations of FloatLib
are evaluated on the same inputs while this module is built, and every input on which they
differ is listed. This is not a proof. It is there to catch a wrong choice in the
specialization, or a different reading of the standard, before the proofs are written.
-/

namespace SoftFloat.FloatLib.Test

open SoftFloat SoftFloat.FloatLib.Spec

def sf : Ops := softfloat Specialization.floatlib

/-- Inputs of `fmt` that reach the special cases: the zeros, the smallest and largest
subnormals, the smallest normal, one, the largest finite values, the infinities, quiet and
signaling NaNs with and without a payload and of both signs, and a few values next to them. -/
def samples (fmt : Format) : List Nat :=
  let f := fmt.fracBits
  let q := 2 ^ (f - 1)
  let one := fmt.pack false fmt.bias 0
  let pos := [
    0, 1, 2 ^ f - 1, 2 ^ f, 2 ^ f + 1,
    one, one + 1, fmt.pack false fmt.bias q, fmt.pack false (fmt.bias + 1) 0,
    fmt.pack false (fmt.bias - f - 1) 0, fmt.pack false (fmt.bias - f - 2) 0,
    fmt.pack false (fmt.expMax - 1) (2 ^ f - 1), fmt.pack false (fmt.expMax - 1) 0,
    fmt.pack false (fmt.expMax / 2) (2 ^ f - 1),
    fmt.pack false fmt.expMax 0,
    fmt.pack false fmt.expMax q, fmt.pack false fmt.expMax (q + 3),
    fmt.pack false fmt.expMax 1, fmt.pack false fmt.expMax 5]
  pos ++ pos.map (· + 2 ^ (fmt.width - 1))

def pairs (xs : List Nat) : List (Nat × Nat) := xs.flatMap fun a => xs.map fun b => (a, b)

structure Mismatch where
  op : String
  inputs : List Nat
  softfloat : Nat × StatusFlags
  floatlib : Nat × StatusFlags
  deriving Repr

def check (op : String) (inputs : List Nat) (s f : Nat × StatusFlags) : List Mismatch :=
  if s = f then [] else [{ op, inputs, softfloat := s, floatlib := f }]

def mismatches (sf : Ops) (fmt : Format) : List Mismatch :=
  let rm := RoundingDirection.roundTiesToEven
  let xs := samples fmt
  let ys := xs.filter fun x => x % 3 = 0 ∨ x ≥ fmt.pack false fmt.expMax 0
  (pairs xs).flatMap (fun (a, b) =>
      check "addition" [a, b] (sf.addition fmt fmt fmt rm a b) (flAdd fmt a b)
      ++ check "subtraction" [a, b] (sf.subtraction fmt fmt fmt rm a b) (flSub fmt a b)
      ++ check "multiplication" [a, b] (sf.multiplication fmt fmt fmt rm a b) (flMul fmt a b)
      ++ check "division" [a, b] (sf.division fmt fmt fmt rm a b) (flDiv fmt a b))
  ++ xs.flatMap (fun a => check "squareRoot" [a] (sf.squareRoot fmt fmt rm a) (flSqrt fmt a))
  ++ (pairs ys).flatMap (fun (a, b) => ys.flatMap fun c =>
      check "fusedMultiplyAdd" [a, b, c] (sf.fusedMultiplyAdd fmt fmt fmt fmt rm a b c) (flFma fmt a b c))

#guard (mismatches sf Format.binary16).isEmpty
#guard (mismatches sf Format.binary32).isEmpty

/-! The comparison tells the choices apart: a specialization that differs from `floatlib` in
one choice differs from FloatLib on some of the inputs. -/

/-- Every NaN result is the canonical NaN, as on RISC-V. -/
def canonicalNaNOnly : Specialization :=
  { Specialization.floatlib with propagateNaN := fun _ dst _ => dst.pack false dst.expMax dst.quietBit }

/-- The sign of a NaN from the second operand of a subtraction is kept. -/
def subtractionSignKept : Specialization :=
  { Specialization.floatlib with propagateNaN := fun _ dst xs => FloatLib.propagateNaN .addition dst xs }

/-- Tininess is detected before rounding. -/
def tininessBeforeRounding : Specialization :=
  { Specialization.floatlib with tininess := .beforeRounding }

#guard !(mismatches (softfloat canonicalNaNOnly) Format.binary32).isEmpty
#guard !(mismatches (softfloat subtractionSignKept) Format.binary32).isEmpty
#guard !(mismatches (softfloat tininessBeforeRounding) Format.binary16).isEmpty
#guard !(mismatches (softfloat tininessBeforeRounding) Format.binary32).isEmpty

end SoftFloat.FloatLib.Test
