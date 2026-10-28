/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: Compare
namespace Format

def orderKeyU (fmt : Format) (u : Unpacked) : Nat :=
  u.expField * 2 ^ fmt.fracBits + u.fracField

def ltU (fmt : Format) (u v : Unpacked) : Bool :=
  if u.sign != v.sign then
    u.sign && !(isZeroU u && isZeroU v)
  else if u.sign then
    fmt.orderKeyU v < fmt.orderKeyU u
  else
    fmt.orderKeyU u < fmt.orderKeyU v

def relation (fa fb : Format) (a b : Nat) : Relation :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  if fa.isNaNU ua || fb.isNaNU ub then .unordered
  else
    let za := isZeroU ua
    let zb := isZeroU ub
    if za && zb then .equal
    else
      let magnitude : Ordering :=
        if fa.isInfU ua && fb.isInfU ub then .eq
        else if fa.isInfU ua then .gt
        else if fb.isInfU ub then .lt
        else
          let qa := fa.ulpExpOf ua
          let qb := fb.ulpExpOf ub
          let q := Min.min qa qb
          Ord.compare (fa.sigOf ua <<< (qa - q).toNat) (fb.sigOf ub <<< (qb - q).toNat)
      let negA := ua.sign && !za
      let negB := ub.sign && !zb
      if negA != negB then (if negA then .lessThan else .greaterThan)
      else
        match (if negA then magnitude.swap else magnitude) with
        | .lt => .lessThan
        | .eq => .equal
        | .gt => .greaterThan

def comparison (fa fb : Format) (signaling : Bool) (holds : Relation → Bool) (a b : Nat) :
    Bool × StatusFlags :=
  let r := relation fa fb a b
  (holds r, { invalidOperation := fa.isSNaNU (fa.unpack a) || fb.isSNaNU (fb.unpack b)
                                  || (signaling && r == .unordered) })

end Format
-- ANCHOR_END: Compare

end SoftFloat
