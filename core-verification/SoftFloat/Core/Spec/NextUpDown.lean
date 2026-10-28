/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Sign
import SoftFloat.Core.Spec.Specialization

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: NextUpDown
def nextNaNResultOf (sp : Specialization) (op : NaNOperation) (fmt : Format) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  r.1 = sp.propagateNaN op fmt [(fmt, x)] ∧ r.2 = { invalidOperation := isSignalingNaN fmt x }

noncomputable def IsLeastGreater (fmt : Format) (x r : Nat) : Prop :=
  isNaN fmt r = false ∧ valE fmt x < valE fmt r
  ∧ ∀ y, fmt.IsEncoding y → isNaN fmt y = false → valE fmt x < valE fmt y → valE fmt r ≤ valE fmt y

noncomputable def NextUpSpecOf (sp : Specialization) (fmt : Format) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  if isNaN fmt x then nextNaNResultOf sp .nextUp fmt x r
  else r.2 = {} ∧
    if classify fmt x = .infinity false then classify fmt r.1 = .infinity false
    else IsLeastGreater fmt x r.1 ∧ (valE fmt r.1 = 0 → classify fmt r.1 = .zero true)

noncomputable def NextDownSpecOf (sp : Specialization) (fmt : Format) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧
  if isNaN fmt x then nextNaNResultOf sp .nextDown fmt x r
  else NextUpSpecOf sp fmt (withSign fmt x (!(fmt.unpack x).sign))
    (withSign fmt r.1 (!(fmt.unpack r.1).sign), r.2)
-- ANCHOR_END: NextUpDown

end SoftFloat.Spec
