/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Classify

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Specialization
def NaNResultValid (fmt : Format) (r : Nat) : Prop :=
  classify fmt r = .quietNaN ∧ fmt.IsEncoding r

def IsNaNOfClass (fmt : Format) (c : FloatClass) (s : Bool) (x : Nat) : Prop :=
  fmt.IsEncoding x ∧ classify fmt x = c ∧ (fmt.unpack x).sign = s

def IsTotalOrderOn (S : Nat → Prop) (le : Nat → Nat → Bool) : Prop :=
  (∀ x y, S x → S y → le x y = true ∨ le y x = true)
  ∧ (∀ x y, S x → S y → le x y = true → le y x = true → x = y)
  ∧ (∀ x y z, S x → S y → S z → le x y = true → le y z = true → le x z = true)

structure Specialization.Valid (sp : Specialization) : Prop where
  propagateNaN : ∀ op dst xs, NaNResultValid dst (sp.propagateNaN op dst xs)
  intOutOfRange : ∀ src rm exact signed w x, sp.intOutOfRange src rm exact signed w x < 2 ^ w
  totalOrderNaN : ∀ fmt c s, (c = .quietNaN ∨ c = .signalingNaN) →
    IsTotalOrderOn (IsNaNOfClass fmt c s) (sp.totalOrderNaN fmt)
  admissiblePayload : ∀ signaling fmt n, sp.admissiblePayload signaling fmt n = true →
    n < 2 ^ (fmt.fracBits - 1) ∧ (signaling = true → n ≠ 0)
  minNumMaxNumOfEqual : ∀ eq fmt x y, sp.minNumMaxNumOfEqual eq fmt x y = x ∨ sp.minNumMaxNumOfEqual eq fmt x y = y
  minNumMagOfEqual : ∀ fmt x y,
    sp.minNumMaxNumOfEqual .minNumMag fmt x y = sp.minNumMaxNumOfEqual .minNum fmt x y
    ∧ sp.minNumMaxNumOfEqual .maxNumMag fmt x y = sp.minNumMaxNumOfEqual .maxNum fmt x y
  minNumMagNaN : ∀ dst xs,
    sp.propagateNaN .minNumMag dst xs = sp.propagateNaN .minNum dst xs
    ∧ sp.propagateNaN .maxNumMag dst xs = sp.propagateNaN .maxNum dst xs
  scaleBOfNaNExponent : ∀ (fmt : Format) rm x n, fmt.IsEncoding (sp.scaleBOfNaNExponent fmt rm x n).1
-- ANCHOR_END: Specialization

end SoftFloat.Spec
