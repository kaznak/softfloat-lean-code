/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.LogB

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Domain
def Domain.addition (fa fb _dst : Format) (_rm : RoundingDirection) (a b : Nat) : Prop :=
  fa.IsEncoding a ∧ fb.IsEncoding b
def Domain.subtraction (fa fb _dst : Format) (_rm : RoundingDirection) (a b : Nat) : Prop :=
  fa.IsEncoding a ∧ fb.IsEncoding b
def Domain.multiplication (fa fb _dst : Format) (_rm : RoundingDirection) (a b : Nat) : Prop :=
  fa.IsEncoding a ∧ fb.IsEncoding b
def Domain.division (fa fb _dst : Format) (_rm : RoundingDirection) (a b : Nat) : Prop :=
  fa.IsEncoding a ∧ fb.IsEncoding b
def Domain.squareRoot (fa _dst : Format) (_rm : RoundingDirection) (a : Nat) : Prop :=
  fa.IsEncoding a
def Domain.fusedMultiplyAdd (fa fb fc _dst : Format) (_rm : RoundingDirection) (a b c : Nat) :
    Prop :=
  fa.IsEncoding a ∧ fb.IsEncoding b ∧ fc.IsEncoding c
def Domain.convertFormat (src _dst : Format) (_rm : RoundingDirection) (a : Nat) : Prop :=
  src.IsEncoding a
def Domain.convertFromInt (_fmt : Format) (_rm : RoundingDirection) (_v : Int) : Prop :=
  True
def Domain.convertToInteger (fmt : Format) (_rm : RoundingDirection) (_exact _signed : Bool)
    (w a : Nat) : Prop :=
  0 < w ∧ fmt.IsEncoding a
def Domain.roundToIntegral (fmt : Format) (_rm : RoundingDirection) (_exact : Bool) (a : Nat) :
    Prop :=
  fmt.IsEncoding a
def Domain.comparison (_fa _fb : Format) (_signaling : Bool) (_holds : Relation → Bool)
    (_a _b : Nat) : Prop :=
  True
def Domain.copy (_fmt : Format) (_x : Nat) : Prop := True
def Domain.negate (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.abs (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.copySign (fmt : Format) (x y : Nat) : Prop := fmt.IsEncoding x ∧ fmt.IsEncoding y
def Domain.minimumNumber (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maximumNumber (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.minimum (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maximum (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.classOf (_fmt : Format) (_x : Nat) : Prop := True
def Domain.isSignMinus (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isNormal (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isFinite (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isZero (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isSubnormal (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isInfinite (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isNaN (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isSignaling (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.isCanonical (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.radix (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.totalOrder (fmt : Format) (x y : Nat) : Prop := fmt.IsEncoding x ∧ fmt.IsEncoding y
def Domain.totalOrderMag (fmt : Format) (x y : Nat) : Prop := fmt.IsEncoding x ∧ fmt.IsEncoding y
def Domain.nextUp (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.nextDown (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.minNum (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maxNum (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.minNumMag (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maxNumMag (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.minimumMagnitude (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.minimumMagnitudeNumber (fmt : Format) (a b : Nat) : Prop :=
  fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maximumMagnitude (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.maximumMagnitudeNumber (fmt : Format) (a b : Nat) : Prop :=
  fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.remainder (fmt : Format) (a b : Nat) : Prop := fmt.IsEncoding a ∧ fmt.IsEncoding b
def Domain.getPayload (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.setPayload (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.setPayloadSignaling (fmt : Format) (x : Nat) : Prop := fmt.IsEncoding x
def Domain.logB (fmt : Format) (lf : LogBFormat) (x : Nat) : Prop :=
  LogBFormat.Valid fmt lf ∧ fmt.IsEncoding x
def Domain.scaleB (fmt : Format) (lf : LogBFormat) (_rm : RoundingDirection) (x n : Nat) : Prop :=
  LogBFormat.Valid fmt lf ∧ fmt.IsEncoding x ∧ ScaleBOperandValid fmt lf n
-- ANCHOR_END: Domain

end SoftFloat.Spec
