/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
namespace SoftFloat

-- ANCHOR: RoundingDirection
inductive RoundingDirection where
  | roundTiesToEven
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero
  | roundTiesToAway
  | roundToOdd
  deriving DecidableEq, Repr
-- ANCHOR_END: RoundingDirection

-- ANCHOR: Relation
inductive Relation where
  | lessThan
  | equal
  | greaterThan
  | unordered
  deriving DecidableEq, Repr
-- ANCHOR_END: Relation

-- ANCHOR: StatusFlags
structure StatusFlags where
  inexact          : Bool := false
  underflow        : Bool := false
  overflow         : Bool := false
  divideByZero     : Bool := false
  invalidOperation : Bool := false
  deriving DecidableEq, Repr

def StatusFlags.union (a b : StatusFlags) : StatusFlags where
  inexact          := a.inexact || b.inexact
  underflow        := a.underflow || b.underflow
  overflow         := a.overflow || b.overflow
  divideByZero     := a.divideByZero || b.divideByZero
  invalidOperation := a.invalidOperation || b.invalidOperation
-- ANCHOR_END: StatusFlags

end SoftFloat
