/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Format
import SoftFloat.RISCV.Base.BF16

namespace SoftFloat.RISCV.Spec

open SoftFloat

-- ANCHOR: Formats
def scalarFormats : List Format := [.binary16, .binary32, .binary64, .binary128]

def conversionPairs : List (Format × Format) :=
  [(.binary32, .binary64), (.binary64, .binary32), (.binary32, .binary128), (.binary128, .binary32),
    (.binary64, .binary128), (.binary128, .binary64), (.binary16, .binary32), (.binary32, .binary16),
    (.binary16, .binary64), (.binary64, .binary16), (.binary16, .binary128), (.binary128, .binary16),
    (.binary32, .bf16), (.bf16, .binary32)]

def wideningPairs : List (Format × Format) := [(.binary16, .binary32), (.binary32, .binary64), (.bf16, .binary32)]

def vectorFormats : List Format := [.binary16, .binary32, .binary64]
-- ANCHOR_END: Formats

end SoftFloat.RISCV.Spec
