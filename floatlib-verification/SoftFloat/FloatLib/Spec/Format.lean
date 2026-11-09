/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import FloatLib.Floats.Formats.BinaryInterchange.Format.Definition

namespace SoftFloat.FloatLib.Spec

open FloatLib.Floats.Formats.BinaryInterchange (FloatFormat)

-- ANCHOR: ToFL
/-- The binary interchange format of FloatLib with the exponent width and the fraction width of
`fmt`, and the IEEE bias and encoding of special values. -/
def toFL (fmt : Format) : FloatFormat :=
  FloatFormat.ieee fmt.expBits fmt.fracBits
    (by have := fmt.expBits_three_le; omega)
    (by have := fmt.sigBits_three_le; unfold Format.fracBits; omega)
-- ANCHOR_END: ToFL

end SoftFloat.FloatLib.Spec
