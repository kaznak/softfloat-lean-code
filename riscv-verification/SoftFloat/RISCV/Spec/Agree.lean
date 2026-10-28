/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.RISCV.Spec.Correct

namespace SoftFloat.RISCV.Spec

open SoftFloat

-- ANCHOR: Agree
structure InstructionAgree (fmt : Format) (o₁ o₂ : InstructionOps fmt) : Prop where
  FADD : ∀ m (a b : BitVec fmt.width), o₁.FADD m a b = o₂.FADD m a b
  FSUB : ∀ m (a b : BitVec fmt.width), o₁.FSUB m a b = o₂.FSUB m a b
  FMUL : ∀ m (a b : BitVec fmt.width), o₁.FMUL m a b = o₂.FMUL m a b
  FDIV : ∀ m (a b : BitVec fmt.width), o₁.FDIV m a b = o₂.FDIV m a b
  FSQRT : ∀ m (a : BitVec fmt.width), o₁.FSQRT m a = o₂.FSQRT m a
  FMIN : ∀ (a b : BitVec fmt.width), o₁.FMIN a b = o₂.FMIN a b
  FMAX : ∀ (a b : BitVec fmt.width), o₁.FMAX a b = o₂.FMAX a b
  FMADD : ∀ m (a b c : BitVec fmt.width), o₁.FMADD m a b c = o₂.FMADD m a b c
  FMSUB : ∀ m (a b c : BitVec fmt.width), o₁.FMSUB m a b c = o₂.FMSUB m a b c
  FNMSUB : ∀ m (a b c : BitVec fmt.width), o₁.FNMSUB m a b c = o₂.FNMSUB m a b c
  FNMADD : ∀ m (a b c : BitVec fmt.width), o₁.FNMADD m a b c = o₂.FNMADD m a b c
  FSGNJ : ∀ (a b : BitVec fmt.width), o₁.FSGNJ a b = o₂.FSGNJ a b
  FSGNJN : ∀ (a b : BitVec fmt.width), o₁.FSGNJN a b = o₂.FSGNJN a b
  FSGNJX : ∀ (a b : BitVec fmt.width), o₁.FSGNJX a b = o₂.FSGNJX a b
  FEQ : ∀ (a b : BitVec fmt.width), o₁.FEQ a b = o₂.FEQ a b
  FLT : ∀ (a b : BitVec fmt.width), o₁.FLT a b = o₂.FLT a b
  FLE : ∀ (a b : BitVec fmt.width), o₁.FLE a b = o₂.FLE a b
  FCLASS : ∀ (a : BitVec fmt.width), o₁.FCLASS a = o₂.FCLASS a
  FCVT_W_F : ∀ m (a : BitVec fmt.width), o₁.FCVT_W_F m a = o₂.FCVT_W_F m a
  FCVT_WU_F : ∀ m (a : BitVec fmt.width), o₁.FCVT_WU_F m a = o₂.FCVT_WU_F m a
  FCVT_L_F : ∀ m (a : BitVec fmt.width), o₁.FCVT_L_F m a = o₂.FCVT_L_F m a
  FCVT_LU_F : ∀ m (a : BitVec fmt.width), o₁.FCVT_LU_F m a = o₂.FCVT_LU_F m a
  FCVT_F_W : ∀ m (x : BitVec 32), o₁.FCVT_F_W m x = o₂.FCVT_F_W m x
  FCVT_F_WU : ∀ m (x : BitVec 32), o₁.FCVT_F_WU m x = o₂.FCVT_F_WU m x
  FCVT_F_L : ∀ m (x : BitVec 64), o₁.FCVT_F_L m x = o₂.FCVT_F_L m x
  FCVT_F_LU : ∀ m (x : BitVec 64), o₁.FCVT_F_LU m x = o₂.FCVT_F_LU m x
  FLI : ∀ (i : BitVec 5), o₁.FLI i = o₂.FLI i
  FMINM : ∀ (a b : BitVec fmt.width), o₁.FMINM a b = o₂.FMINM a b
  FMAXM : ∀ (a b : BitVec fmt.width), o₁.FMAXM a b = o₂.FMAXM a b
  FROUND : ∀ m (a : BitVec fmt.width), o₁.FROUND m a = o₂.FROUND m a
  FROUNDNX : ∀ m (a : BitVec fmt.width), o₁.FROUNDNX m a = o₂.FROUNDNX m a
  FLEQ : ∀ (a b : BitVec fmt.width), o₁.FLEQ a b = o₂.FLEQ a b
  FLTQ : ∀ (a b : BitVec fmt.width), o₁.FLTQ a b = o₂.FLTQ a b
  FCVTMOD_W_D : ∀ (a : BitVec fmt.width), InstructionDomain.FCVTMOD_W_D fmt a →
    o₁.FCVTMOD_W_D a = o₂.FCVTMOD_W_D a

structure ConversionAgree (src dst : Format) (o₁ o₂ : ConversionOps src dst) : Prop where
  FCVT : ∀ m (a : BitVec src.width), o₁.FCVT m a = o₂.FCVT m a

structure WideningAgree (narrow wide : Format) (o₁ o₂ : WideningOps narrow wide) : Prop where
  VFWADD : ∀ m (a b : BitVec narrow.width), o₁.VFWADD m a b = o₂.VFWADD m a b
  VFWSUB : ∀ m (a b : BitVec narrow.width), o₁.VFWSUB m a b = o₂.VFWSUB m a b
  VFWMUL : ∀ m (a b : BitVec narrow.width), o₁.VFWMUL m a b = o₂.VFWMUL m a b
  VFWADD_W : ∀ m (a : BitVec wide.width) (b : BitVec narrow.width), o₁.VFWADD_W m a b = o₂.VFWADD_W m a b
  VFWSUB_W : ∀ m (a : BitVec wide.width) (b : BitVec narrow.width), o₁.VFWSUB_W m a b = o₂.VFWSUB_W m a b
  VFWMACC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width), o₁.VFWMACC m a b c = o₂.VFWMACC m a b c
  VFWNMACC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    o₁.VFWNMACC m a b c = o₂.VFWNMACC m a b c
  VFWMSAC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width), o₁.VFWMSAC m a b c = o₂.VFWMSAC m a b c
  VFWNMSAC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    o₁.VFWNMSAC m a b c = o₂.VFWNMSAC m a b c
  VFWREDOSUM : ∀ m (init : BitVec wide.width) (xs : List (BitVec narrow.width)),
    o₁.VFWREDOSUM m init xs = o₂.VFWREDOSUM m init xs
  VFNCVT_ROD_F_F_W : ∀ (a : BitVec wide.width), o₁.VFNCVT_ROD_F_F_W a = o₂.VFNCVT_ROD_F_F_W a

structure VectorAgree (fmt : Format) (o₁ o₂ : VectorOps fmt) : Prop where
  VFRSQRT7 : ∀ (a : BitVec fmt.width), o₁.VFRSQRT7 a = o₂.VFRSQRT7 a
  VFREC7 : ∀ m (a : BitVec fmt.width), o₁.VFREC7 m a = o₂.VFREC7 m a
  VMFNE : ∀ (a b : BitVec fmt.width), o₁.VMFNE a b = o₂.VMFNE a b
  VMFGT : ∀ (a b : BitVec fmt.width), o₁.VMFGT a b = o₂.VMFGT a b
  VMFGE : ∀ (a b : BitVec fmt.width), o₁.VMFGE a b = o₂.VMFGE a b
  VFCVT_X_F_V : ∀ m (a : BitVec fmt.width), o₁.VFCVT_X_F_V m a = o₂.VFCVT_X_F_V m a
  VFCVT_XU_F_V : ∀ m (a : BitVec fmt.width), o₁.VFCVT_XU_F_V m a = o₂.VFCVT_XU_F_V m a
  VFCVT_F_X_V : ∀ m (x : BitVec fmt.width), o₁.VFCVT_F_X_V m x = o₂.VFCVT_F_X_V m x
  VFCVT_F_XU_V : ∀ m (x : BitVec fmt.width), o₁.VFCVT_F_XU_V m x = o₂.VFCVT_F_XU_V m x
  VFNCVT_X_F_W : ∀ m (a : BitVec fmt.width), o₁.VFNCVT_X_F_W m a = o₂.VFNCVT_X_F_W m a
  VFNCVT_XU_F_W : ∀ m (a : BitVec fmt.width), o₁.VFNCVT_XU_F_W m a = o₂.VFNCVT_XU_F_W m a
  VFWCVT_F_X_V : ∀ m (x : BitVec (fmt.width / 2)), o₁.VFWCVT_F_X_V m x = o₂.VFWCVT_F_X_V m x
  VFWCVT_F_XU_V : ∀ m (x : BitVec (fmt.width / 2)), o₁.VFWCVT_F_XU_V m x = o₂.VFWCVT_F_XU_V m x
  VFREDOSUM : ∀ m (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    o₁.VFREDOSUM m init xs = o₂.VFREDOSUM m init xs
  VFREDMIN : ∀ (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    o₁.VFREDMIN init xs = o₂.VFREDMIN init xs
  VFREDMAX : ∀ (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    o₁.VFREDMAX init xs = o₂.VFREDMAX init xs
-- ANCHOR_END: Agree

-- ANCHOR: RiscvAgree
structure RiscvAgree (o₁ o₂ : RiscvOps) : Prop where
  instructions : ∀ fmt ∈ scalarFormats, InstructionAgree fmt (o₁.instructions fmt) (o₂.instructions fmt)
  conversions : ∀ p ∈ conversionPairs, ConversionAgree p.1 p.2 (o₁.conversions p.1 p.2) (o₂.conversions p.1 p.2)
  widenings : ∀ p ∈ wideningPairs, WideningAgree p.1 p.2 (o₁.widenings p.1 p.2) (o₂.widenings p.1 p.2)
  vectorOps : ∀ fmt ∈ vectorFormats, VectorAgree fmt (o₁.vectorOps fmt) (o₂.vectorOps fmt)
  decode : ∀ (rm frm : BitVec 3), o₁.decode rm frm = o₂.decode rm frm
  toFflags : ∀ f, o₁.toFflags f = o₂.toFflags f
-- ANCHOR_END: RiscvAgree

end SoftFloat.RISCV.Spec
