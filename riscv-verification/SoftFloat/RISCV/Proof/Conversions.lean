/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Correctness
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Formats

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem conversions_correct (src dst : Format) :
    ConversionCorrect Specialization.riscv src dst (riscv.conversions src dst) where
  FCVT m a :=
    have h := riscv_softfloat_correct.convertFormat src dst m.toRoundingDirection a.toNat a.isLt
    spec_bitsResult h (convertFormat_isEncoding riscv_valid h)

end SoftFloat.RISCV.Proof
