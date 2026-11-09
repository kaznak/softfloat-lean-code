/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format

namespace SoftFloat.FloatLib

-- ANCHOR: SpecializationFloatLib
/-- The first entry of `xs` that `p` holds of, with its position counted from `i`. -/
def firstWith (p : Format × Nat → Bool) : List (Format × Nat) → Nat → Option (Nat × Format × Nat)
  | [], _ => none
  | x :: xs, i => if p x then some (i, x) else firstWith p xs (i + 1)

/-- The sign of the NaN taken from the operand at the position `i`, whose sign is `s`. FloatLib
subtracts by adding the negated second operand, so a NaN from the second operand of a
subtraction has its sign reversed. -/
def nanSign : NaNOperation → Nat → Bool → Bool
  | .subtraction, 1, s => !s
  | _, _, s => s

/-- The quiet NaN of `dst` with the sign `s` and the payload `payload`, or the payload zero when
`payload` does not fit below the quiet bit of `dst`. -/
def nanOf (dst : Format) (s : Bool) (payload : Nat) : Nat :=
  dst.pack s dst.expMax (dst.quietBit + if payload < dst.quietBit then payload else 0)

/-- The NaN that FloatLib delivers: the first signaling NaN of the operands, or else the first
NaN, quieted, with its sign (`nanSign`) and payload; and the positive NaN with the quiet bit alone when no operand is a NaN. -/
def propagateNaN (op : NaNOperation) (dst : Format) (xs : List (Format × Nat)) : Nat :=
  let isS := fun (x : Format × Nat) => x.1.isSNaNU (x.1.unpack x.2)
  let isN := fun (x : Format × Nat) => x.1.isNaNU (x.1.unpack x.2)
  match (firstWith isS xs 0).orElse fun _ => firstWith isN xs 0 with
  | none => dst.pack false dst.expMax dst.quietBit
  | some (i, f, x) =>
      let u := f.unpack x
      nanOf dst (nanSign op i u.sign) (u.fracField % f.quietBit)

/-- The specialization with the choices of FloatLib for the arithmetic operations. The fields
`setPayloadSign`, `intOutOfRange`, `totalOrderNaN`, `admissiblePayload`,
`minNumMaxNumOfEqual` and `scaleBOfNaNExponent` do not stand for choices of FloatLib: the
operations compared with FloatLib do not read them, and they are the simplest values that make
the specialization valid. -/
def _root_.SoftFloat.Specialization.floatlib : Specialization where
  propagateNaN := propagateNaN
  setPayloadSign := fun _ _ _ => false
  fusedMultiplyAddZeroInfinityQuietNaNInvalid := true
  tininess := .afterRounding
  intOutOfRange := fun _ _ _ _ _ _ => 0
  totalOrderNaN := fun _ x y => decide (x ≤ y)
  admissiblePayload := fun _ _ _ => false
  minNumMaxNumOfEqual := fun _ _ x _ => x
  scaleBOfNaNExponent := fun fmt _ _ _ => (fmt.pack false fmt.expMax fmt.quietBit, {})
-- ANCHOR_END: SpecializationFloatLib

end SoftFloat.FloatLib
