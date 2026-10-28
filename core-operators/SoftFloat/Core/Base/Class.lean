/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
namespace SoftFloat

-- ANCHOR: Class
inductive Class where
  | signalingNaN
  | quietNaN
  | negativeInfinity
  | negativeNormal
  | negativeSubnormal
  | negativeZero
  | positiveZero
  | positiveSubnormal
  | positiveNormal
  | positiveInfinity
  deriving DecidableEq, Repr
-- ANCHOR_END: Class

end SoftFloat
