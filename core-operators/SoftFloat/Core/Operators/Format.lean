/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base

namespace SoftFloat

-- ANCHOR: Classification
namespace Format

def quietBit (fmt : Format) : Nat := 2 ^ (fmt.fracBits - 1)

def isNaNU (fmt : Format) (u : Unpacked) : Bool :=
  u.expField == fmt.expMax && u.fracField != 0
def isSNaNU (fmt : Format) (u : Unpacked) : Bool :=
  fmt.isNaNU u && u.fracField < fmt.quietBit

def isInfU (fmt : Format) (u : Unpacked) : Bool :=
  u.expField == fmt.expMax && u.fracField == 0
def isZeroU (u : Unpacked) : Bool :=
  u.expField == 0 && u.fracField == 0

def isNormalU (fmt : Format) (u : Unpacked) : Bool :=
  u.expField != 0 && u.expField != fmt.expMax
def isSubnormalU (u : Unpacked) : Bool :=
  u.expField == 0 && u.fracField != 0

end Format
-- ANCHOR_END: Classification

-- ANCHOR: ClassOperation
namespace Format

def classOf (fmt : Format) (n : Nat) : Class :=
  let u := fmt.unpack n
  if fmt.isNaNU u then
    if fmt.isSNaNU u then .signalingNaN else .quietNaN
  else if fmt.isInfU u then
    if u.sign then .negativeInfinity else .positiveInfinity
  else if isZeroU u then
    if u.sign then .negativeZero else .positiveZero
  else if isSubnormalU u then
    if u.sign then .negativeSubnormal else .positiveSubnormal
  else
    if u.sign then .negativeNormal else .positiveNormal

end Format
-- ANCHOR_END: ClassOperation

end SoftFloat
