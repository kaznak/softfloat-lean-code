/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Result
import SoftFloat.Core.Spec.TotalOrder

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Payload
def IsNonNegativeIntegerOf (fmt : Format) (x n : Nat) : Prop :=
  IsFinite fmt x ∧ (fmt.unpack x).sign = false ∧ valR fmt x = n

def IsAdmissiblePayload (sp : Specialization) (fmt : Format) (signaling : Bool) (n : Nat) : Prop :=
  sp.admissiblePayload signaling fmt n = true

def GetPayloadSpecOf (fmt : Format) (x : Nat) (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧ r.2 = {} ∧
  if isNaN fmt x then IsNonNegativeIntegerOf fmt r.1 (nanPayload fmt x)
  else IsFinite fmt r.1 ∧ valR fmt r.1 = -1

def setPayloadResultOf (sp : Specialization) (signaling : Bool) (fmt : Format) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  fmt.IsEncoding r.1 ∧ r.2 = {}
  ∧ (∀ n, IsNonNegativeIntegerOf fmt x n → IsAdmissiblePayload sp fmt signaling n →
      classify fmt r.1 = (if signaling then .signalingNaN else .quietNaN)
      ∧ (fmt.unpack r.1).sign = sp.setPayloadSign signaling fmt n ∧ nanPayload fmt r.1 = n)
  ∧ ((∀ n, IsNonNegativeIntegerOf fmt x n → ¬ IsAdmissiblePayload sp fmt signaling n) →
      classify fmt r.1 = .zero false)

def SetPayloadSpecOf (sp : Specialization) (fmt : Format) (x : Nat) (r : Nat × StatusFlags) : Prop :=
  setPayloadResultOf sp false fmt x r

def SetPayloadSignalingSpecOf (sp : Specialization) (fmt : Format) (x : Nat)
    (r : Nat × StatusFlags) : Prop :=
  setPayloadResultOf sp true fmt x r
-- ANCHOR_END: Payload

end SoftFloat.Spec
