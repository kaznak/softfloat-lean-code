/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Correctness
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Specialization

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof

theorem riscv_softfloat_correct : Correct Specialization.riscv (softfloat Specialization.riscv) :=
  softfloat_correct Specialization.riscv riscv_valid

theorem binary16_correct : FormatCorrect Specialization.riscv .binary16 riscv.F16 :=
  perFormat_correct riscv_valid riscv_softfloat_correct .binary16

theorem binary32_correct : FormatCorrect Specialization.riscv .binary32 riscv.F32 :=
  perFormat_correct riscv_valid riscv_softfloat_correct .binary32

theorem binary64_correct : FormatCorrect Specialization.riscv .binary64 riscv.F64 :=
  perFormat_correct riscv_valid riscv_softfloat_correct .binary64

theorem binary128_correct : FormatCorrect Specialization.riscv .binary128 riscv.F128 :=
  perFormat_correct riscv_valid riscv_softfloat_correct .binary128

end SoftFloat.RISCV.Proof
