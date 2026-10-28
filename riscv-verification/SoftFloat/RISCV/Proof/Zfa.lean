/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.ConvertToInteger
import SoftFloat.RISCV.Spec.Zfa
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Formats
import SoftFloat.RISCV.Proof.ZfaGeneric

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem binary32_loadImmediate_correct :
    ∀ i, LoadImmediateValueOf .binary32 (loadImmediateEntry i.toNat) (loadImmediate .binary32 i).toNat := by
  refine bitVec5_cases (fun k hk => ?_)
  interval_cases k
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := true) (m := 8388608) (e := -23) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact ⟨by decide, valR_of_fields (s := false) (m := 2 ^ 23) (e := -149) (by decide) (by decide) (by decide) (by decide) (two_pow_mul_two_zpow 23 (-149) _ (by decide))⟩
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -39) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -38) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -31) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -30) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -27) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -26) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -25) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 10485760) (e := -25) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 12582912) (e := -25) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 14680064) (e := -25) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 10485760) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 12582912) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 14680064) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -23) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 10485760) (e := -23) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 12582912) (e := -23) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 14680064) (e := -23) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -22) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 10485760) (e := -22) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 12582912) (e := -22) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -21) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -20) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -19) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -16) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -15) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -8) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 8388608) (e := -7) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · show classify Format.binary32 (loadImmediate .binary32 30#5).toNat = .infinity false
    decide
  · show (loadImmediate .binary32 31#5).toNat = canonicalNaN Format.binary32
    decide

theorem binary64_loadImmediate_correct :
    ∀ i, LoadImmediateValueOf .binary64 (loadImmediateEntry i.toNat) (loadImmediate .binary64 i).toNat := by
  refine bitVec5_cases (fun k hk => ?_)
  interval_cases k
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := true) (m := 4503599627370496) (e := -52) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact ⟨by decide, valR_of_fields (s := false) (m := 2 ^ 52) (e := -1074) (by decide) (by decide) (by decide) (by decide) (two_pow_mul_two_zpow 52 (-1074) _ (by decide))⟩
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -68) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -67) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -60) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -59) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -56) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -55) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -54) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5629499534213120) (e := -54) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6755399441055744) (e := -54) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7881299347898368) (e := -54) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -53) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5629499534213120) (e := -53) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6755399441055744) (e := -53) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7881299347898368) (e := -53) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -52) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5629499534213120) (e := -52) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6755399441055744) (e := -52) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7881299347898368) (e := -52) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -51) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5629499534213120) (e := -51) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6755399441055744) (e := -51) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -50) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -49) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -48) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -45) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -44) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -37) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 4503599627370496) (e := -36) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · show classify Format.binary64 (loadImmediate .binary64 30#5).toNat = .infinity false
    decide
  · show (loadImmediate .binary64 31#5).toNat = canonicalNaN Format.binary64
    decide

theorem binary128_loadImmediate_correct :
    ∀ i, LoadImmediateValueOf .binary128 (loadImmediateEntry i.toNat) (loadImmediate .binary128 i).toNat := by
  refine bitVec5_cases (fun k hk => ?_)
  interval_cases k
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := true) (m := 5192296858534827628530496329220096) (e := -112) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact ⟨by decide, valR_of_fields (s := false) (m := 2 ^ 112) (e := -16494) (by decide) (by decide) (by decide) (by decide) (two_pow_mul_two_zpow 112 (-16494) _ (by decide))⟩
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -128) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -127) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -120) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -119) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -116) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -115) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -114) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6490371073168534535663120411525120) (e := -114) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7788445287802241442795744493830144) (e := -114) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 9086519502435948349928368576135168) (e := -114) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -113) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6490371073168534535663120411525120) (e := -113) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7788445287802241442795744493830144) (e := -113) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 9086519502435948349928368576135168) (e := -113) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -112) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6490371073168534535663120411525120) (e := -112) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7788445287802241442795744493830144) (e := -112) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 9086519502435948349928368576135168) (e := -112) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -111) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 6490371073168534535663120411525120) (e := -111) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 7788445287802241442795744493830144) (e := -111) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -110) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -109) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -108) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -105) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -104) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -97) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 5192296858534827628530496329220096) (e := -96) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · show classify Format.binary128 (loadImmediate .binary128 30#5).toNat = .infinity false
    decide
  · show (loadImmediate .binary128 31#5).toNat = canonicalNaN Format.binary128
    decide

theorem binary16_loadImmediate_correct :
    ∀ i, LoadImmediateValueOf .binary16 (loadImmediateEntry i.toNat) (loadImmediate .binary16 i).toNat := by
  refine bitVec5_cases (fun k hk => ?_)
  interval_cases k
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := true) (m := 1024) (e := -10) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact ⟨by decide, valR_of_fields (s := false) (m := 2 ^ 10) (e := -24) (by decide) (by decide) (by decide) (by decide) (two_pow_mul_two_zpow 10 (-24) _ (by decide))⟩
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 256) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 512) (e := -24) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -18) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -17) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -14) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -13) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -12) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1280) (e := -12) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1536) (e := -12) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1792) (e := -12) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -11) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1280) (e := -11) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1536) (e := -11) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1792) (e := -11) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -10) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1280) (e := -10) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1536) (e := -10) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1792) (e := -10) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -9) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1280) (e := -9) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1536) (e := -9) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -8) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -7) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -6) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -3) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := -2) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · exact loadImmediate_value (BitVec.isLt _) (by decide) (valR_of_fields (s := false) (m := 1024) (e := 5) (by decide) (by decide) (by decide) (by decide) (by norm_num))
  · refine loadImmediate_overflow ?_ (by decide)
    rw [maxFinite_eq, show emax Format.binary16 - (Format.binary16.fracBits : ℤ) = 5 by decide,
      show Format.binary16.sigBits = 11 by rfl]
    norm_num
  · show classify Format.binary16 (loadImmediate .binary16 30#5).toNat = .infinity false
    decide
  · show (loadImmediate .binary16 31#5).toNat = canonicalNaN Format.binary16
    decide

theorem toNat_emod_two_pow_1025_emod (n : Int) :
    (n % (2 ^ 1025 : Int)).toNat % 2 ^ 32 = (n % (2 ^ 32 : Int)).toNat := by
  have h1 : 0 ≤ n % (2 ^ 1025 : Int) := Int.emod_nonneg _ (by positivity)
  have h2 : 0 ≤ n % (2 ^ 32 : Int) := Int.emod_nonneg _ (by positivity)
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Int.natCast_mod, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2,
    Int.natCast_pow]
  exact Int.emod_emod_of_dvd n (pow_dvd_pow 2 (by norm_num))

theorem fcvtmod_w_d_eq (a : BitVec 64) :
    (riscv.instructions .binary64).FCVTMOD_W_D a =
      if (Format.binary64.unpack a.toNat).expField = Format.binary64.expMax then
        (0#32, (riscv.F64.convertToInteger .roundTowardZero true true 32 a).2)
      else ((riscv.F64.convertToInteger .roundTowardZero true true 1025 a).1.setWidth 32,
        (riscv.F64.convertToInteger .roundTowardZero true true 32 a).2) :=
  rfl

set_option exponentiation.threshold 1100 in
theorem fcvtmod_w_d_spec (a : BitVec 64) :
    ModularConvertToIntegerSpecOf .binary64 a.toNat (bitsResult ((riscv.instructions .binary64).FCVTMOD_W_D a)) := by
  have hW : ConvertToIntegerSpecOf Specialization.riscv .binary64 .roundTowardZero true true 32 a.toNat
      (bitsResult (riscv.F64.convertToInteger .roundTowardZero true true 32 a)) :=
    binary64_correct.convertToInteger .roundTowardZero true true 32 a (by decide)
  have hX : ConvertToIntegerSpecOf Specialization.riscv .binary64 .roundTowardZero true true 1025 a.toNat
      (bitsResult (riscv.F64.convertToInteger .roundTowardZero true true 1025 a)) :=
    binary64_correct.convertToInteger .roundTowardZero true true 1025 a (by decide)
  have hfin := isFinite_iff Format.binary64 a.toNat
  unfold ConvertToIntegerSpecOf at hW hX
  unfold ModularConvertToIntegerSpecOf
  have hflags : ((riscv.instructions .binary64).FCVTMOD_W_D a).2 =
      (riscv.F64.convertToInteger .roundTowardZero true true 32 a).2 := by
    rw [fcvtmod_w_d_eq]; split <;> rfl
  cases hc : classify Format.binary64 a.toNat with
  | quietNaN | signalingNaN | infinity s =>
    have hnf : ¬ IsFinite Format.binary64 a.toNat := by unfold IsFinite; rw [hc]; exact id
    have hexp : (Format.binary64.unpack a.toNat).expField = Format.binary64.expMax := by
      by_contra h; exact hnf (hfin.2 h)
    simp only [hc] at hW
    have h2 := congrArg Prod.snd hW
    simp only [bitsResult] at h2 ⊢
    refine Prod.ext ?_ ?_
    · rw [fcvtmod_w_d_eq]
      simp only [hexp, ↓reduceIte]
      rfl
    · rw [hflags, h2]
  | normal s | subnormal s | zero s =>
    have hf : IsFinite Format.binary64 a.toNat := by unfold IsFinite; rw [hc]; trivial
    have hexp : (Format.binary64.unpack a.toNat).expField ≠ Format.binary64.expMax := hfin.1 hf
    simp only [hc] at hW hX ⊢
    have hb := abs_valR_lt Format.binary64 hf
    rw [show emax Format.binary64 + 1 = ((1024 : ℕ) : ℤ) by decide, zpow_natCast,
      show (2 : ℝ) ^ 1024 = ((2 ^ 1024 : ℕ) : ℝ) by norm_num] at hb
    obtain ⟨hlo, hhi⟩ := integralPartOf_roundTowardZero_bounds s hb
    generalize integralPartOf .roundTowardZero s (valR Format.binary64 a.toNat) = n at hlo hhi hW hX ⊢
    have hlo' : ¬ n < intRangeLo true 1025 := by
      unfold intRangeLo; norm_num at hlo ⊢; omega
    have hhi' : ¬ intRangeHi true 1025 < n := by
      unfold intRangeHi; norm_num at hhi ⊢; omega
    simp only [hlo', hhi', ↓reduceIte] at hX
    obtain ⟨hX1, -⟩ := hX
    simp only [bitsResult] at hX1 hW ⊢
    refine ⟨?_, ?_⟩
    · rw [fcvtmod_w_d_eq]
      simp only [hexp, ↓reduceIte]
      rw [BitVec.toNat_setWidth, hX1]
      exact toNat_emod_two_pow_1025_emod n
    · rw [hflags]
      by_cases hlo32 : n < intRangeLo true 32
      · simp only [hlo32, ↓reduceIte, true_or] at hW ⊢; exact congrArg Prod.snd hW
      · simp only [hlo32, ↓reduceIte, false_or] at hW ⊢
        by_cases hhi32 : intRangeHi true 32 < n
        · simp only [hhi32, ↓reduceIte] at hW ⊢; exact congrArg Prod.snd hW
        · simp only [hhi32, ↓reduceIte] at hW ⊢; exact hW.2

theorem binary64_modularConvertToInteger_correct :
    ∀ (a : BitVec 64),
      ModularConvertToIntegerSpecOf .binary64 a.toNat (bitsResult ((riscv.instructions .binary64).FCVTMOD_W_D a)) :=
  fun a => fcvtmod_w_d_spec a

end SoftFloat.RISCV.Proof
