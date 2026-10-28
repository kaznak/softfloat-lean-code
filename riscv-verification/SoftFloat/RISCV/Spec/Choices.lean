/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Specialization
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Convert
import SoftFloat.RISCV.Base.BF16

namespace SoftFloat.RISCV.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: Riscv
def canonicalNaN (fmt : Format) : Nat :=
  fmt.pack false fmt.expMax (2 ^ (fmt.fracBits - 1))

def riscvIntOutOfRange (src : Format) (signed : Bool) (w x : Nat) : Nat :=
  let v := if isNaN src x = true ∨ (src.unpack x).sign = false then intRangeHi signed w else intRangeLo signed w
  (v % (2 ^ w : Int)).toNat

structure RiscvChoices (sp : Specialization) : Prop where
  propagateNaN : ∀ op dst xs, sp.propagateNaN op dst xs = canonicalNaN dst
  bf16CanonicalNaN : ∀ op xs, sp.propagateNaN op .bf16 xs = 0x7FC0
  fusedMultiplyAddZeroInfinityQuietNaNInvalid : sp.fusedMultiplyAddZeroInfinityQuietNaNInvalid = true
  tininess : sp.tininess = .afterRounding
  intOutOfRange : ∀ src rm exact signed w x, sp.intOutOfRange src rm exact signed w x = riscvIntOutOfRange src signed w x
-- ANCHOR_END: Riscv

end SoftFloat.RISCV.Spec
