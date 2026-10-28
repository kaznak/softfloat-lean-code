/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Result
import SoftFloat.Core.Spec.Arith

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Remainder
def IsNearestIntegerTiesToEven (v : ℝ) (n : ℤ) : Prop :=
  (∀ m : ℤ, |(n : ℝ) - v| ≤ |(m : ℝ) - v|) ∧ (|(n : ℝ) - v| = 1 / 2 → Even n)

def RemainderSpecOf (sp : Specialization) (fmt : Format) (a b : Nat) (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  if isNaN fmt a || isNaN fmt b then
    r.1 = sp.propagateNaN .remainder fmt [(fmt, a), (fmt, b)]
    ∧ r.2 = { invalidOperation := isSignalingNaN fmt a || isSignalingNaN fmt b }
  else if arithIsInf fmt a || arithIsZero fmt b then
    r.1 = sp.propagateNaN .remainder fmt [(fmt, a), (fmt, b)] ∧ r.2 = { invalidOperation := true }
  else if arithIsInf fmt b then
    r.1 = a ∧ r.2 = {}
  else
    IsFinite fmt r.1
    ∧ (∃ n : ℤ, IsNearestIntegerTiesToEven (valR fmt a / valR fmt b) n
        ∧ valR fmt r.1 = valR fmt a - valR fmt b * n)
    ∧ (valR fmt r.1 = 0 → classify fmt r.1 = .zero (arithSign fmt a))
    ∧ r.2 = {}
-- ANCHOR_END: Remainder

end SoftFloat.Spec
