/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Ops
import SoftFloat.Core.Base.FormatOps

namespace SoftFloat

-- ANCHOR: PerFormat
def perFormat (o : Ops) (fmt : Format) : FormatOps fmt where
  addition rm a b :=
    let r := o.addition fmt fmt fmt rm a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  subtraction rm a b :=
    let r := o.subtraction fmt fmt fmt rm a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  multiplication rm a b :=
    let r := o.multiplication fmt fmt fmt rm a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  division rm a b :=
    let r := o.division fmt fmt fmt rm a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  squareRoot rm a :=
    let r := o.squareRoot fmt fmt rm a.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  fusedMultiplyAdd rm a b c :=
    let r := o.fusedMultiplyAdd fmt fmt fmt fmt rm a.toNat b.toNat c.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  roundToIntegral rm exact a :=
    let r := o.roundToIntegral fmt rm exact a.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  compareQuietEqual a b :=
    o.comparison fmt fmt false (· == .equal) a.toNat b.toNat
  compareSignalingEqual a b :=
    o.comparison fmt fmt true (· == .equal) a.toNat b.toNat
  compareSignalingLess a b :=
    o.comparison fmt fmt true (· == .lessThan) a.toNat b.toNat
  compareQuietLess a b :=
    o.comparison fmt fmt false (· == .lessThan) a.toNat b.toNat
  compareSignalingLessEqual a b :=
    o.comparison fmt fmt true (fun r => r == .lessThan || r == .equal) a.toNat b.toNat
  compareQuietLessEqual a b :=
    o.comparison fmt fmt false (fun r => r == .lessThan || r == .equal) a.toNat b.toNat
  convertFormat rm dst a :=
    let r := o.convertFormat fmt dst rm a.toNat
    (BitVec.ofNat dst.width r.1, r.2)
  convertToInteger rm exact signed w a :=
    let r := o.convertToInteger fmt rm exact signed w a.toNat
    (BitVec.ofNat w r.1, r.2)
  convertFromInt rm signed _ x :=
    let r := o.convertFromInt fmt rm (if signed then x.toInt else (x.toNat : Int))
    (BitVec.ofNat fmt.width r.1, r.2)
  copy a := BitVec.ofNat fmt.width (o.copy fmt a.toNat)
  abs a := BitVec.ofNat fmt.width (o.abs fmt a.toNat)
  negate a := BitVec.ofNat fmt.width (o.negate fmt a.toNat)
  copySign a b := BitVec.ofNat fmt.width (o.copySign fmt a.toNat b.toNat)
  classOf a := o.classOf fmt a.toNat
  minimumNumber a b :=
    let r := o.minimumNumber fmt a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  maximumNumber a b :=
    let r := o.maximumNumber fmt a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  minimum a b :=
    let r := o.minimum fmt a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
  maximum a b :=
    let r := o.maximum fmt a.toNat b.toNat
    (BitVec.ofNat fmt.width r.1, r.2)
-- ANCHOR_END: PerFormat

end SoftFloat
