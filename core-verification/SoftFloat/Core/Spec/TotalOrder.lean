/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Sign

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: TotalOrder
def nanPayload (fmt : Format) (x : Nat) : Nat :=
  (fmt.unpack x).fracField % 2 ^ (fmt.fracBits - 1)

noncomputable def TotalOrderSpecOf (sp : Specialization) (fmt : Format) (x y : Nat) (r : Bool) : Prop :=
  let sx := (fmt.unpack x).sign
  let sy := (fmt.unpack y).sign
  if isNaN fmt x = false ∧ isNaN fmt y = false then
    (valE fmt x < valE fmt y → r = true)
    ∧ (valE fmt y < valE fmt x → r = false)
    ∧ (valE fmt x = valE fmt y →
        (classify fmt x = .zero true → classify fmt y = .zero false → r = true)
        ∧ (classify fmt x = .zero false → classify fmt y = .zero true → r = false)
        ∧ (sx = sy →
            (r = true ↔ if sx = true ∧ sy = true
              then fmt.ulpExpOf (fmt.unpack x) ≥ fmt.ulpExpOf (fmt.unpack y)
              else fmt.ulpExpOf (fmt.unpack x) ≤ fmt.ulpExpOf (fmt.unpack y))))
  else if isNaN fmt y = false then r = sx
  else if isNaN fmt x = false then r = !sy
  else if sx ≠ sy then r = sx
  else if classify fmt x = .signalingNaN ∧ classify fmt y = .quietNaN then r = !sx
  else if classify fmt x = .quietNaN ∧ classify fmt y = .signalingNaN then r = sx
  else r = sp.totalOrderNaN fmt x y

noncomputable def TotalOrderMagSpecOf (sp : Specialization) (fmt : Format) (x y : Nat) (r : Bool) : Prop :=
  TotalOrderSpecOf sp fmt (withSign fmt x false) (withSign fmt y false) r
-- ANCHOR_END: TotalOrder

end SoftFloat.Spec
