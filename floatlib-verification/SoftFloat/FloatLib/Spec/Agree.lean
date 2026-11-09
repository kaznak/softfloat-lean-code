/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Arith
import SoftFloat.Core.Base.Ops
import SoftFloat.FloatLib.Spec.Ops

/-!
# What is claimed of FloatLib

On the range compared — addition, subtraction, multiplication, division, square root and fused
multiply-add, rounded to nearest with ties to even, with the operands and the result in one
format, on every bit string of the format — the operations of FloatLib meet the specification
of Core (`FloatLibMeetsSpec`), and a group of operations computes what FloatLib computes
(`FloatLibAgree`).
-/

namespace SoftFloat.FloatLib.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: FloatLibMeetsSpec
/-- The operations of FloatLib meet the specification of Core with the specialization `sp`. -/
structure FloatLibMeetsSpec (sp : Specialization) : Prop where
  addition : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    AdditionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flAdd fmt a b)
  subtraction : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    SubtractionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flSub fmt a b)
  multiplication : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    MultiplicationSpecOf sp fmt fmt fmt .roundTiesToEven a b (flMul fmt a b)
  division : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    DivisionSpecOf sp fmt fmt fmt .roundTiesToEven a b (flDiv fmt a b)
  squareRoot : ∀ fmt a, fmt.IsEncoding a →
    SquareRootSpecOf sp fmt fmt .roundTiesToEven a (flSqrt fmt a)
  fusedMultiplyAdd : ∀ fmt a b c, fmt.IsEncoding a → fmt.IsEncoding b → fmt.IsEncoding c →
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt .roundTiesToEven a b c (flFma fmt a b c)
-- ANCHOR_END: FloatLibMeetsSpec

-- ANCHOR: FloatLibAgree
/-- The group of operations `o` computes, bit for bit and flag for flag, what FloatLib
computes. -/
structure FloatLibAgree (o : Ops) : Prop where
  addition : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    o.addition fmt fmt fmt .roundTiesToEven a b = flAdd fmt a b
  subtraction : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    o.subtraction fmt fmt fmt .roundTiesToEven a b = flSub fmt a b
  multiplication : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    o.multiplication fmt fmt fmt .roundTiesToEven a b = flMul fmt a b
  division : ∀ fmt a b, fmt.IsEncoding a → fmt.IsEncoding b →
    o.division fmt fmt fmt .roundTiesToEven a b = flDiv fmt a b
  squareRoot : ∀ fmt a, fmt.IsEncoding a →
    o.squareRoot fmt fmt .roundTiesToEven a = flSqrt fmt a
  fusedMultiplyAdd : ∀ fmt a b c, fmt.IsEncoding a → fmt.IsEncoding b → fmt.IsEncoding c →
    o.fusedMultiplyAdd fmt fmt fmt fmt .roundTiesToEven a b c = flFma fmt a b c
-- ANCHOR_END: FloatLibAgree

end SoftFloat.FloatLib.Spec
