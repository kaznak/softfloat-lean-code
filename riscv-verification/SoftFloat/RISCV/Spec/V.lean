/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.RISCV.Spec.Choices

namespace SoftFloat.RISCV.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: VSpec
def reciprocalSquareRootEstimateTable : List Nat :=
  [52, 51, 50, 48, 47, 46, 44, 43, 42, 41, 40, 39, 38, 36, 35, 34,
   33, 32, 31, 30, 30, 29, 28, 27, 26, 25, 24, 23, 23, 22, 21, 20,
   19, 19, 18, 17, 16, 16, 15, 14, 14, 13, 12, 12, 11, 10, 10, 9,
   9, 8, 7, 7, 6, 6, 5, 4, 4, 3, 3, 2, 2, 1, 1, 0,
   127, 125, 123, 121, 119, 118, 116, 114, 113, 111, 109, 108, 106, 105, 103, 102,
   100, 99, 97, 96, 95, 93, 92, 91, 90, 88, 87, 86, 85, 84, 83, 82,
   80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 70, 69, 68, 67, 66,
   65, 64, 63, 63, 62, 61, 60, 59, 59, 58, 57, 56, 56, 55, 54, 53]

def reciprocalEstimateTable : List Nat :=
  [127, 125, 123, 121, 119, 117, 116, 114, 112, 110, 109, 107, 105, 104, 102, 100,
   99, 97, 96, 94, 93, 91, 90, 88, 87, 85, 84, 83, 81, 80, 79, 77,
   76, 75, 74, 72, 71, 70, 69, 68, 66, 65, 64, 63, 62, 61, 60, 59,
   58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43,
   42, 41, 40, 40, 39, 38, 37, 36, 35, 35, 34, 33, 32, 31, 31, 30,
   29, 28, 28, 27, 26, 25, 25, 24, 23, 23, 22, 21, 21, 20, 19, 19,
   18, 17, 17, 16, 15, 15, 14, 14, 13, 12, 12, 11, 11, 10, 9, 9,
   8, 8, 7, 7, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1, 0]

def normalizedExponent (fmt : Format) (u : Format.Unpacked) : Int :=
  if u.expField = 0 then -((fmt.fracBits - (Nat.log2 u.fracField + 1) : Nat) : Int) else u.expField

def normalizedSignificand (fmt : Format) (u : Format.Unpacked) : Nat :=
  if u.expField = 0 then u.fracField * 2 ^ (1 - normalizedExponent fmt u).toNat % 2 ^ fmt.fracBits
  else u.fracField

def ReciprocalSquareRootEstimateSpecOf (fmt : Format) (a : Nat) (r : Nat × StatusFlags) : Prop :=
  match classify fmt a with
  | .quietNaN => r = (canonicalNaN fmt, {})
  | .signalingNaN => r = (canonicalNaN fmt, { invalidOperation := true })
  | .infinity true => r = (canonicalNaN fmt, { invalidOperation := true })
  | .infinity false => r = (fmt.pack false 0 0, {})
  | .zero s => r = (fmt.pack s fmt.expMax 0, { divideByZero := true })
  | .normal true | .subnormal true => r = (canonicalNaN fmt, { invalidOperation := true })
  | .normal false | .subnormal false =>
    let u := fmt.unpack a
    let e := normalizedExponent fmt u
    let sig := reciprocalSquareRootEstimateTable.getD
      ((e % 2).toNat * 64 + normalizedSignificand fmt u / 2 ^ (fmt.fracBits - 6)) 0
    r = (fmt.pack false ((3 * (fmt.bias : Int) - 1 - e) / 2).toNat (sig * 2 ^ (fmt.fracBits - 7)), {})

def reciprocalEstimateOverflowIsInfinite : RoundingDirection → Bool → Bool
  | .roundTowardNegative, true => true
  | .roundTiesToEven, true => true
  | .roundTiesToAway, true => true
  | .roundTowardPositive, true => false
  | .roundTowardZero, true => false
  | .roundTowardPositive, false => true
  | .roundTiesToEven, false => true
  | .roundTiesToAway, false => true
  | .roundTowardNegative, false => false
  | .roundTowardZero, false => false
  | .roundToOdd, _ => false

def ReciprocalEstimateSpecOf (fmt : Format) (rm : RoundingDirection) (a : Nat) (r : Nat × StatusFlags) : Prop :=
  match classify fmt a with
  | .quietNaN => r = (canonicalNaN fmt, {})
  | .signalingNaN => r = (canonicalNaN fmt, { invalidOperation := true })
  | .infinity s => r = (fmt.pack s 0 0, {})
  | .zero s => r = (fmt.pack s fmt.expMax 0, { divideByZero := true })
  | .normal s | .subnormal s =>
    let u := fmt.unpack a
    if u.expField = 0 ∧ u.fracField < 2 ^ (fmt.fracBits - 2) then
      r = (if reciprocalEstimateOverflowIsInfinite rm s then fmt.pack s fmt.expMax 0
           else fmt.pack s (fmt.expMax - 1) (2 ^ fmt.fracBits - 1), { inexact := true, overflow := true })
    else
      let oe : Int := 2 * (fmt.bias : Int) - 1 - normalizedExponent fmt u
      let sig := reciprocalEstimateTable.getD (normalizedSignificand fmt u / 2 ^ (fmt.fracBits - 7)) 0
        * 2 ^ (fmt.fracBits - 7)
      if oe = 0 ∨ oe = -1 then r = (fmt.pack s 0 ((2 ^ fmt.fracBits + sig) / 2 ^ (1 - oe).toNat), {})
      else r = (fmt.pack s oe.toNat sig, {})

def OrderedReductionOf (step : Nat → Nat → Nat × StatusFlags → Prop) : Nat → List Nat → Nat × StatusFlags → Prop
  | a, [], r => r = (a, {})
  | a, x :: xs, r => ∃ s t, step a x s ∧ OrderedReductionOf step s.1 xs t ∧ r = (t.1, s.2.union t.2)

inductive SumTree where
  | leaf (fmt : Format) (x : Nat)
  | node (fmt : Format) (l r : SumTree)
  | identity (fmt : Format) (t : SumTree)

def SumTree.leaves : SumTree → List (Format × Nat)
  | .leaf fmt x => [(fmt, x)]
  | .node _ l r => l.leaves ++ r.leaves
  | .identity _ t => t.leaves

def SumTree.isLeaf : SumTree → Bool
  | .leaf _ _ => true
  | _ => false

def SumTree.identityCount : SumTree → Nat
  | .leaf _ _ => 0
  | .node _ l r => l.identityCount + r.identityCount
  | .identity _ t => t.identityCount + 1

def additiveIdentity (fmt : Format) (rm : RoundingDirection) : Nat :=
  fmt.pack (rm != .roundTowardNegative) 0 0

def AtLeastAsWide (fmt f : Format) : Prop := fmt.expBits ≤ f.expBits ∧ fmt.sigBits ≤ f.sigBits

def SumTreeResultOf (sp : Specialization) (acc : Format) (rm : RoundingDirection) :
    SumTree → Format × Nat × StatusFlags → Prop
  | .leaf f x, r => r = (f, x, {})
  | .node f l t, r => AtLeastAsWide acc f ∧ ∃ a b s, SumTreeResultOf sp acc rm l a ∧ SumTreeResultOf sp acc rm t b
      ∧ AdditionSpecOf sp a.1 b.1 f rm a.2.1 b.2.1 s ∧ r = (f, s.1, (a.2.2.union b.2.2).union s.2)
  | .identity f t, r => AtLeastAsWide acc f ∧ ∃ a s, SumTreeResultOf sp acc rm t a
      ∧ AdditionSpecOf sp a.1 acc f rm a.2.1 (additiveIdentity acc rm) s ∧ r = (f, s.1, a.2.2.union s.2)

def UnorderedSumOf (sp : Specialization) (acc elem : Format) (rm : RoundingDirection) (inactive : Nat) (init : Nat)
    (xs : List Nat) (r : Nat × StatusFlags) : Prop :=
  ∃ t : SumTree, t.leaves.Perm ((acc, init) :: xs.map (elem, ·)) ∧ t.identityCount ≤ inactive
    ∧ ∃ v, SumTreeResultOf sp acc rm t v
    ∧ ∃ c : Nat × StatusFlags,
      (((¬ t.isLeaf ∨ 0 < inactive) ∧ ∃ d, ConvertFormatSpecOf sp v.1 acc rm v.2.1 d ∧ c = (d.1, v.2.2.union d.2))
       ∨ (t.isLeaf ∧ c = (v.2.1, v.2.2)))
      ∧ (r = c ∨ ∃ s, AdditionSpecOf sp acc acc acc rm c.1 (additiveIdentity acc rm) s ∧ r = (s.1, c.2.union s.2))

inductive ReductionTree where
  | leaf (x : Nat)
  | node (l r : ReductionTree)

def ReductionTree.leaves : ReductionTree → List Nat
  | .leaf x => [x]
  | .node l r => l.leaves ++ r.leaves

def ReductionTreeResultOf (step : Nat → Nat → Nat × StatusFlags → Prop) :
    ReductionTree → Nat × StatusFlags → Prop
  | .leaf x, r => r = (x, {})
  | .node l t, r => ∃ a b s, ReductionTreeResultOf step l a ∧ ReductionTreeResultOf step t b ∧ step a.1 b.1 s
      ∧ r = (s.1, (a.2.union b.2).union s.2)

def OrderIndependentReductionOf (step : Nat → Nat → Nat × StatusFlags → Prop) (init : Nat) (xs : List Nat)
    (r : Nat × StatusFlags) : Prop :=
  ∀ (t : ReductionTree) (v : Nat × StatusFlags), t.leaves.Perm (init :: xs) → ReductionTreeResultOf step t v → v = r

-- ANCHOR_END: VSpec

end SoftFloat.RISCV.Spec
