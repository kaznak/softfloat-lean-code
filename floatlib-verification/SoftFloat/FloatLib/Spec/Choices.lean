/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Specialization
import SoftFloat.Core.Spec.Compare

namespace SoftFloat.FloatLib.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: FloatLibChoices
/-- The arithmetic operations compared with FloatLib. -/
def IsArithmetic (op : NaNOperation) : Prop :=
  op = .addition ∨ op = .subtraction ∨ op = .multiplication ∨ op = .division
    ∨ op = .squareRoot ∨ op = .fusedMultiplyAdd

/-- The position and the entry of the first operand of `xs` that `p` holds of. -/
def firstNaN (p : Format → Nat → Bool) : List (Format × Nat) → Nat → Option (Nat × Format × Nat)
  | [], _ => none
  | (f, x) :: xs, i => if p f x then some (i, f, x) else firstNaN p xs (i + 1)

/-- The sign of the NaN taken from the operand at the position `i`, whose sign is `s`: reversed
for the second operand of a subtraction, which FloatLib computes by adding the negated second
operand, and kept otherwise. -/
def floatLibNaNSign : NaNOperation → Nat → Bool → Bool
  | .subtraction, 1, s => !s
  | _, _, s => s

/-- The NaN that FloatLib delivers. The first signaling NaN among the operands, or else the
first NaN, is quieted, keeping its sign and its payload (the fraction field without the quiet
bit), and the payload becomes zero when it does not fit below the quiet bit of `dst`. The sign
is reversed for the second operand of a subtraction (`floatLibNaNSign`). When no operand is a NaN, the result is the positive NaN of `dst` whose
fraction field is the quiet bit alone. -/
def floatLibNaN (op : NaNOperation) (dst : Format) (xs : List (Format × Nat)) : Nat :=
  let q := 2 ^ (dst.fracBits - 1)
  match (firstNaN isSignalingNaN xs 0).orElse fun _ => firstNaN isNaN xs 0 with
  | none => dst.pack false dst.expMax q
  | some (i, f, x) =>
      let u := f.unpack x
      let p := u.fracField % 2 ^ (f.fracBits - 1)
      dst.pack (floatLibNaNSign op i u.sign) dst.expMax (q + if p < q then p else 0)

/-- The choices of FloatLib, on the fields of a specialization that the arithmetic operations
read. -/
structure FloatLibChoices (sp : Specialization) : Prop where
  propagateNaN : ∀ op dst xs, IsArithmetic op → sp.propagateNaN op dst xs = floatLibNaN op dst xs
  fusedMultiplyAddZeroInfinityQuietNaNInvalid : sp.fusedMultiplyAddZeroInfinityQuietNaNInvalid = true
  tininess : sp.tininess = .afterRounding
-- ANCHOR_END: FloatLibChoices

end SoftFloat.FloatLib.Spec
