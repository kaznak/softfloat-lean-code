/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.RISCV.Spec.Choices

namespace SoftFloat.RISCV.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: ZfaSpec
inductive LoadImmediateEntry where
  | value (x : ℝ)
  | minPositiveNormal
  | infinity
  | canonicalNaN

noncomputable def loadImmediateEntry : Nat → LoadImmediateEntry
  | 0 => .value (-1)
  | 1 => .minPositiveNormal
  | 2 => .value (2 ^ (-16 : ℤ))
  | 3 => .value (2 ^ (-15 : ℤ))
  | 4 => .value (2 ^ (-8 : ℤ))
  | 5 => .value (2 ^ (-7 : ℤ))
  | 6 => .value 0.0625
  | 7 => .value 0.125
  | 8 => .value 0.25
  | 9 => .value 0.3125
  | 10 => .value 0.375
  | 11 => .value 0.4375
  | 12 => .value 0.5
  | 13 => .value 0.625
  | 14 => .value 0.75
  | 15 => .value 0.875
  | 16 => .value 1
  | 17 => .value 1.25
  | 18 => .value 1.5
  | 19 => .value 1.75
  | 20 => .value 2
  | 21 => .value 2.5
  | 22 => .value 3
  | 23 => .value 4
  | 24 => .value 8
  | 25 => .value 16
  | 26 => .value 128
  | 27 => .value 256
  | 28 => .value (2 ^ (15 : ℕ))
  | 29 => .value (2 ^ (16 : ℕ))
  | 30 => .infinity
  | _ => .canonicalNaN

def LoadImmediateValueOf (fmt : Format) : LoadImmediateEntry → Nat → Prop
  | .value x, r =>
    ((∃ n, fmt.IsEncoding n ∧ IsFinite fmt n ∧ valR fmt n = x) → IsFinite fmt r ∧ valR fmt r = x)
    ∧ ((¬ ∃ n, fmt.IsEncoding n ∧ IsFinite fmt n ∧ valR fmt n = x) → classify fmt r = .infinity false)
  | .minPositiveNormal, r => classify fmt r = .normal false ∧ valR fmt r = 2 ^ emin fmt
  | .infinity, r => classify fmt r = .infinity false
  | .canonicalNaN, r => r = canonicalNaN fmt

def ModularConvertToIntegerSpecOf (fmt : Format) (a : Nat) (r : Nat × StatusFlags) : Prop :=
  match classify fmt a with
  | .quietNaN | .signalingNaN | .infinity _ => r = (0, { invalidOperation := true })
  | .normal s | .subnormal s | .zero s =>
    let n := integralPartOf .roundTowardZero s (valR fmt a)
    r.1 = (n % (2 ^ 32 : Int)).toNat
    ∧ if n < intRangeLo true 32 ∨ intRangeHi true 32 < n then r.2 = { invalidOperation := true }
      else integralFlagsOf true ((n : ℝ) ≠ valR fmt a) r.2
-- ANCHOR_END: ZfaSpec

end SoftFloat.RISCV.Spec
