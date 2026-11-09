/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types
import FloatLib.Numerics.IEEEStatus

namespace SoftFloat.FloatLib.Spec

-- ANCHOR: FlagsOf
/-- The five exception flags of FloatLib, each to the flag of the same exception. -/
def flagsOf (s : FloatLib.Numerics.IEEEStatus) : StatusFlags where
  inexact := s.inexact
  underflow := s.underflow
  overflow := s.overflow
  divideByZero := s.divideByZero
  invalidOperation := s.invalid
-- ANCHOR_END: FlagsOf

end SoftFloat.FloatLib.Spec
