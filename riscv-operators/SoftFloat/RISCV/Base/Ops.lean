/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Base.Format
import SoftFloat.Core.Base.FormatOps
import SoftFloat.RISCV.Base.RoundingMode

namespace SoftFloat.RISCV

-- ANCHOR: InstructionOps
structure InstructionOps (fmt : Format) where
  FADD : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FSUB : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMUL : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FDIV : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FSQRT : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMIN : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMAX : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMADD : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMSUB : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FNMSUB : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FNMADD : RoundingMode → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FSGNJ : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width
  FSGNJN : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width
  FSGNJX : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width
  FEQ : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  FLT : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  FLE : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  FCLASS : BitVec fmt.width → BitVec 10
  FCVT_W_F : RoundingMode → BitVec fmt.width → BitVec 32 × StatusFlags
  FCVT_WU_F : RoundingMode → BitVec fmt.width → BitVec 32 × StatusFlags
  FCVT_L_F : RoundingMode → BitVec fmt.width → BitVec 64 × StatusFlags
  FCVT_LU_F : RoundingMode → BitVec fmt.width → BitVec 64 × StatusFlags
  FCVT_F_W : RoundingMode → BitVec 32 → BitVec fmt.width × StatusFlags
  FCVT_F_WU : RoundingMode → BitVec 32 → BitVec fmt.width × StatusFlags
  FCVT_F_L : RoundingMode → BitVec 64 → BitVec fmt.width × StatusFlags
  FCVT_F_LU : RoundingMode → BitVec 64 → BitVec fmt.width × StatusFlags
  FLI : BitVec 5 → BitVec fmt.width
  FMINM : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FMAXM : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FROUND : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FROUNDNX : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  FLEQ : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  FLTQ : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  FCVTMOD_W_D : BitVec fmt.width → BitVec 32 × StatusFlags
-- ANCHOR_END: InstructionOps

-- ANCHOR: ConversionOps
structure ConversionOps (src dst : Format) where
  FCVT : RoundingMode → BitVec src.width → BitVec dst.width × StatusFlags
-- ANCHOR_END: ConversionOps

-- ANCHOR: WideningOps
structure WideningOps (narrow wide : Format) where
  VFWADD : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width × StatusFlags
  VFWSUB : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width × StatusFlags
  VFWMUL : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width × StatusFlags
  VFWADD_W : RoundingMode → BitVec wide.width → BitVec narrow.width → BitVec wide.width × StatusFlags
  VFWSUB_W : RoundingMode → BitVec wide.width → BitVec narrow.width → BitVec wide.width × StatusFlags
  VFWMACC : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width →
    BitVec wide.width × StatusFlags
  VFWNMACC : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width →
    BitVec wide.width × StatusFlags
  VFWMSAC : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width →
    BitVec wide.width × StatusFlags
  VFWNMSAC : RoundingMode → BitVec narrow.width → BitVec narrow.width → BitVec wide.width →
    BitVec wide.width × StatusFlags
  VFWREDOSUM : RoundingMode → BitVec wide.width → List (BitVec narrow.width) → BitVec wide.width × StatusFlags
  VFNCVT_ROD_F_F_W : BitVec wide.width → BitVec narrow.width × StatusFlags
-- ANCHOR_END: WideningOps

-- ANCHOR: VectorOps
structure VectorOps (fmt : Format) where
  VFRSQRT7 : BitVec fmt.width → BitVec fmt.width × StatusFlags
  VFREC7 : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  VMFNE : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  VMFGT : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  VMFGE : BitVec fmt.width → BitVec fmt.width → Bool × StatusFlags
  VFCVT_X_F_V : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  VFCVT_XU_F_V : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  VFCVT_F_X_V : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  VFCVT_F_XU_V : RoundingMode → BitVec fmt.width → BitVec fmt.width × StatusFlags
  VFNCVT_X_F_W : RoundingMode → BitVec fmt.width → BitVec (fmt.width / 2) × StatusFlags
  VFNCVT_XU_F_W : RoundingMode → BitVec fmt.width → BitVec (fmt.width / 2) × StatusFlags
  VFWCVT_F_X_V : RoundingMode → BitVec (fmt.width / 2) → BitVec fmt.width × StatusFlags
  VFWCVT_F_XU_V : RoundingMode → BitVec (fmt.width / 2) → BitVec fmt.width × StatusFlags
  VFREDOSUM : RoundingMode → BitVec fmt.width → List (BitVec fmt.width) → BitVec fmt.width × StatusFlags
  VFREDMIN : BitVec fmt.width → List (BitVec fmt.width) → BitVec fmt.width × StatusFlags
  VFREDMAX : BitVec fmt.width → List (BitVec fmt.width) → BitVec fmt.width × StatusFlags
-- ANCHOR_END: VectorOps

-- ANCHOR: RiscvOps
structure RiscvOps where
  instructions : (fmt : Format) → InstructionOps fmt
  conversions : (src dst : Format) → ConversionOps src dst
  widenings : (narrow wide : Format) → WideningOps narrow wide
  vectorOps : (fmt : Format) → VectorOps fmt
  decode : BitVec 3 → BitVec 3 → Option RoundingMode
  F16 : FormatOps .binary16
  F32 : FormatOps .binary32
  F64 : FormatOps .binary64
  F128 : FormatOps .binary128
  toFflags : StatusFlags → Nat
-- ANCHOR_END: RiscvOps

end SoftFloat.RISCV
