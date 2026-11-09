/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.FloatLib.Spec.Format
import SoftFloat.FloatLib.Spec.Flags
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

namespace SoftFloat.FloatLib.Spec

open FloatLib.Floats.Formats.BinaryInterchange (Model)

-- ANCHOR: FloatLibOps
/-- An outcome of FloatLib as the bit string of its value and the flags of its status. -/
def ofOutcome {fmt : Format} (o : Model.IEEEOutcome (toFL fmt)) : Nat × StatusFlags :=
  (o.value.toNatBits, flagsOf o.status)

/-- The bit string `a` as a value of FloatLib in the format `fmt`. -/
def ofBits (fmt : Format) (a : Nat) : Model (toFL fmt) :=
  Model.ofNatBits a

/-! The public operations of FloatLib, rounded to nearest with ties to even and with the status
of the exceptions, on bit strings of the format `fmt`. -/

def flAdd (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.add (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true))

def flSub (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.sub (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true))

def flMul (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.mul (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true))

def flDiv (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.div (ofBits fmt a) (ofBits fmt b) (mode := .nearest) (status := true))

def flSqrt (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.sqrt (ofBits fmt a) (mode := .nearest) (status := true))

def flFma (fmt : Format) (a b c : Nat) : Nat × StatusFlags :=
  ofOutcome (Model.fma (ofBits fmt a) (ofBits fmt b) (ofBits fmt c) (mode := .nearest) (status := true))
-- ANCHOR_END: FloatLibOps

end SoftFloat.FloatLib.Spec
