/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: Sign
namespace Format

def flipSign (fmt : Format) (n : Nat) : Nat :=
  if n < 2 ^ (fmt.width - 1) then n + 2 ^ (fmt.width - 1) else n - 2 ^ (fmt.width - 1)

def signBitOf (fmt : Format) (n : Nat) : Nat :=
  n / 2 ^ (fmt.width - 1) % 2

def clearSign (fmt : Format) (n : Nat) : Nat :=
  n % 2 ^ (fmt.width - 1)

def copy (_fmt : Format) (n : Nat) : Nat :=
  n

def abs (fmt : Format) (n : Nat) : Nat :=
  fmt.clearSign n

def negate (fmt : Format) (n : Nat) : Nat :=
  fmt.flipSign n

def copySign (fmt : Format) (a b : Nat) : Nat :=
  fmt.clearSign a + fmt.signBitOf b * 2 ^ (fmt.width - 1)

end Format
-- ANCHOR_END: Sign

end SoftFloat
