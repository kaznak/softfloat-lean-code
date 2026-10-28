/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: Payload
namespace Format

def ofNatExact (fmt : Format) (n : Nat) : Nat :=
  if n = 0 then 0
  else fmt.pack false (fmt.bias + n.log2) ((n - 2 ^ n.log2) * 2 ^ (fmt.fracBits - n.log2))

def minusOne (fmt : Format) : Nat :=
  fmt.pack true fmt.bias 0

def payloadOfInteger (fmt : Format) (a : Nat) : Option Nat :=
  let u := fmt.unpack a
  if u.sign then none
  else if u.expField = 0 then
    if u.fracField = 0 then some 0 else none
  else if fmt.bias ≤ u.expField ∧ u.expField - fmt.bias + 1 < fmt.fracBits
      ∧ u.fracField % 2 ^ (fmt.fracBits - (u.expField - fmt.bias)) = 0 then
    some (2 ^ (u.expField - fmt.bias) + u.fracField / 2 ^ (fmt.fracBits - (u.expField - fmt.bias)))
  else none

def getPayload (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  if fmt.isNaNU u then (fmt.ofNatExact (u.fracField % fmt.quietBit), {})
  else (fmt.minusOne, {})

def setPayload (spec : Specialization) (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  match fmt.payloadOfInteger a with
  | some n =>
    if spec.admissiblePayload false fmt n then
      (fmt.pack (spec.setPayloadSign false fmt n) fmt.expMax (fmt.quietBit + n), {})
    else (0, {})
  | none => (0, {})

def setPayloadSignaling (spec : Specialization) (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  match fmt.payloadOfInteger a with
  | some n =>
    if spec.admissiblePayload true fmt n then (fmt.pack (spec.setPayloadSign true fmt n) fmt.expMax n, {})
    else (0, {})
  | none => (0, {})

end Format
-- ANCHOR_END: Payload

end SoftFloat
