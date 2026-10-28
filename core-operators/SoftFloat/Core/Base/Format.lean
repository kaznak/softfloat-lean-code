/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types

namespace SoftFloat

-- ANCHOR: Format
structure Format where
  expBits : Nat
  sigBits : Nat
  expBits_three_le : 3 ≤ expBits := by decide
  sigBits_three_le : 3 ≤ sigBits := by decide
  sigBits_le_two_pow : sigBits ≤ 2 ^ (expBits - 1) := by decide
  deriving DecidableEq, Repr

namespace Format

def binary16 : Format := ⟨5, 11, by decide, by decide, by decide⟩
def binary32 : Format := ⟨8, 24, by decide, by decide, by decide⟩
def binary64 : Format := ⟨11, 53, by decide, by decide, by decide⟩
def binary128 : Format := ⟨15, 113, by decide, by decide, by decide⟩

def fracBits (fmt : Format) : Nat := fmt.sigBits - 1
def width (fmt : Format) : Nat := fmt.expBits + fmt.sigBits
def bias (fmt : Format) : Nat := 2 ^ (fmt.expBits - 1) - 1
def expMax (fmt : Format) : Nat := 2 ^ fmt.expBits - 1
def minQ (fmt : Format) : Int := 1 - (fmt.bias : Int) - (fmt.fracBits : Int)

def IsEncoding (fmt : Format) (a : Nat) : Prop := a < 2 ^ fmt.width

theorem expBits_two_le (fmt : Format) : 2 ≤ fmt.expBits := by
  have := fmt.expBits_three_le
  omega

theorem sigBits_two_le (fmt : Format) : 2 ≤ fmt.sigBits := by
  have := fmt.sigBits_three_le
  omega

theorem fracBits_le_bias (fmt : Format) : fmt.fracBits ≤ fmt.bias := by
  have := fmt.sigBits_le_two_pow
  unfold fracBits bias
  omega

end Format
-- ANCHOR_END: Format

-- ANCHOR: Encoding
namespace Format

structure Unpacked where
  sign : Bool
  expField : Nat
  fracField : Nat
  deriving DecidableEq, Repr

def unpack (fmt : Format) (n : Nat) : Unpacked where
  sign := n / 2 ^ (fmt.width - 1) % 2 == 1
  expField := n / 2 ^ fmt.fracBits % 2 ^ fmt.expBits
  fracField := n % 2 ^ fmt.fracBits
def pack (fmt : Format) (s : Bool) (e f : Nat) : Nat :=
  ((if s then 1 else 0) * 2 ^ fmt.expBits + e) * 2 ^ fmt.fracBits + f

def sigOf (fmt : Format) (u : Unpacked) : Nat :=
  if u.expField = 0 then u.fracField else 2 ^ fmt.fracBits + u.fracField

def ulpExpOf (fmt : Format) (u : Unpacked) : Int :=
  (if u.expField = 0 then 1 else (u.expField : Int)) - fmt.bias - fmt.fracBits

end Format
-- ANCHOR_END: Encoding

end SoftFloat
