# SoftFloatLean

[English](README.md) | [日本語](README.ja.md)

[IEEE 754](https://standards.ieee.org/ieee/754/6210/) binary floating-point arithmetic in [Lean](https://lean-lang.org/).

## Packages

For each target (Core and RISCV), this repository contains two packages: one on the operations side and one on the
verification side. Core is the part that does not depend on the target and that each target specializes; RISCV is the
RISC-V specialization and the groups of instructions. Module names are `SoftFloat.<target>.<layer>.…`.

| Package name | Directory | Layers (module prefixes) | Contents | Mathlib |
|---|---|---|---|---|
| softfloat-core-operators | `core-operators/` | Base (`SoftFloat.Core.Base`), Operators (`SoftFloat.Core.Operators`) | The vocabulary shared by the specification and the operations (formats and their parameters, decoding and encoding, rounding directions (the five rounding-direction attributes of IEEE 754 and round-to-odd), flags, the list of operations and the type `Ops`, and the type `FormatOps` of the per-format groups of functions), and the executable implementation of the IEEE 754 operations (`softfloat sp`, which takes a specialization as an argument, and `perFormat`, which builds the per-format groups of functions). | Not needed |
| softfloat-core-verification | `core-verification/` | Spec (`SoftFloat.Core.Spec`), Proof (`SoftFloat.Core.Proof`), Claim (`SoftFloat.Core.Claim`) | Definitions that state what it means for an implementation to be correct, in terms of real (`ℝ`) values and rounding (`Correct`, `FormatCorrect`, and others), their proofs, and the theorems finally proved (`SoftFloat.Claim.correctness` and `SoftFloat.Claim.uniqueness`). | Needed |
| softfloat-riscv-operators | `riscv-operators/` | Base (`SoftFloat.RISCV.Base`), Operators (`SoftFloat.RISCV.Operators`) | Base is the RISC-V vocabulary shared by the specification and the operations: the types of the four groups of instructions (`InstructionOps fmt` for scalar instructions, `ConversionOps src dst` for conversions between formats, `WideningOps narrow wide` for vector widening operations, and `VectorOps fmt` for vector element operations not among the scalar instructions); the type of the RISC-V group of operations (`RiscvOps`), which bundles these with the decoding of rm, the per-format groups of functions, and the map to the bits of fflags; the rounding mode (`RoundingMode`); and the BF16 format (`Format.bf16`). Operators are the RISC-V value `riscv` (the entry point for users: instructions are called as fields of the groups that are fields of the value, such as `(riscv.instructions .binary32).FADD` and `(riscv.conversions .binary64 .binary32).FCVT`; the decoding of the rm field and frm is `riscv.decode`; the per-format groups of functions on `BitVec` are `riscv.F16` to `riscv.F128`; and the map from a set of flags to the value of fflags is `riscv.toFflags`) and, beneath it, the value of the RISC-V specialization (`Specialization.riscv`). Results match down to the bit pattern. | Not needed |
| softfloat-riscv-verification | `riscv-verification/` | Spec (`SoftFloat.RISCV.Spec`), Proof (`SoftFloat.RISCV.Proof`), Claim (`SoftFloat.RISCV.Claim`), Test (`SoftFloat.RISCV.Test`) | The predicate of the RISC-V choices (`RiscvChoices`); the formats and pairs of formats that RISC-V has; the predicates of correctness, preconditions and agreement for each group of instructions (`InstructionCorrect`, `InstructionAgree`, and others) and the predicates of correctness and agreement of the RISC-V group of operations that bundle them (`RiscvCorrect` and `RiscvAgree`), with the coverage checks; their proofs; the theorems finally proved (`SoftFloat.RISCV.Claim.correctness` and `SoftFloat.RISCV.Claim.uniqueness`); and differential comparison against Berkeley TestFloat (an IEEE 754 conformance tester) (`testfloat/`). | Needed |

- The dependencies between packages go `core-operators/` ← `core-verification/`, `core-operators/` ← `riscv-operators/`, and
  `riscv-operators/` and `core-verification/` ← `riscv-verification/`. The operations side depends on neither the verification
  side nor Mathlib, and Core does not depend on RISCV.
- Within a target, the layers go Base ← Operators, Base ← Spec, and Spec and Operators ← Proof ← Claim (Spec depends on neither
  Operators nor Proof). A RISCV layer may depend on the same layer of Core and the layers below it, and Test depends only on the
  RISCV Operators. The directions inside the verification side cannot be enforced by Lake, so
  `scripts/check-package-dependencies.sh` checks them from the imports of the modules.
- What you read to trust correctness is all of Base and Spec of both targets, and the statements of the Claim theorems of
  both. Operators, Proof and Test are left to the Lean proofs and the results of the comparison.
- Users `require` a package on the operations side and write `import SoftFloat.Core.Operators` (the Core operations and the Base
  vocabulary) or `import SoftFloat.RISCV.Operators` (up to the RISC-V value `riscv`). The operations side does not depend on
  Mathlib, so Mathlib does not come along.

### How to require

From the lakefile of your project, `require` the one package for the part you want to use. The packages are in directories
at the top of the repository, so when you `require` from git, put that directory in `subDir`.

**Which one to require**

| What you want to use | Package to require (`name`) | `subDir` | import | Mathlib |
|---|---|---|---|---|
| Choose a specialization yourself and use the operations generic over formats (`softfloat sp`) | softfloat-core-operators | `core-operators` | `import SoftFloat.Core.Operators` | Not needed |
| Use the RISC-V instructions (`(SoftFloat.RISCV.riscv.instructions .binary32).FADD` and others) | softfloat-riscv-operators | `riscv-operators` | `import SoftFloat.RISCV.Operators` | Not needed |
| Use the Core specification and theorems (`SoftFloat.Spec.Correct`, `SoftFloat.Claim.correctness`, and others) | softfloat-core-verification | `core-verification` | `import SoftFloat.Core.Spec`, `import SoftFloat.Core.Claim`, and others | Needed |
| Use the RISC-V specification and theorems (`RiscvChoices`, `RiscvCorrect`, `SoftFloat.RISCV.Claim.correctness`, and others) | softfloat-riscv-verification | `riscv-verification` | `import SoftFloat.RISCV.Spec.Agree` (up to `RiscvChoices`, `RiscvCorrect` and `RiscvAgree`), `import SoftFloat.RISCV.Claim`, and others | Needed |

A package automatically pulls in, from the same repository, the packages it requires (the `[[require]]` entries of its
`lakefile.toml`, in the directions given under "Packages" above): softfloat-riscv-operators and softfloat-core-verification
each pull in softfloat-core-operators, and softfloat-riscv-verification pulls in softfloat-riscv-operators and
softfloat-core-verification (and through them softfloat-core-operators). For example, `import SoftFloat.RISCV.Operators`
gives you the Core operations and the Base vocabulary as well. **Do not require a package that another package you require
already pulls in.** If you require both, the same repository is fetched twice, and if you also write different `rev`s, the
package that requires the other uses the one you wrote directly, and the versions disagree without warning. If you do need to
list both, write the same `rev`.

**In lakefile.toml** (replace `git` and `rev` with the URL of this repository and the commit or tag you use)

```toml
[[require]]
name = "softfloat-riscv-operators"
git = "<URL of this repository>"
rev = "<commit or tag>"
subDir = "riscv-operators"
```

**In lakefile.lean**

```lean
require «softfloat-riscv-operators» from git
  "<URL of this repository>" @ "<commit or tag>" / "riscv-operators"
```

**Example of use**

```lean
import SoftFloat.RISCV.Operators

open SoftFloat

-- FADD.S: 1.0 + 2.0 (rounding mode RNE). Returns the pair of the result bits and the flags.
#eval ((RISCV.riscv.instructions .binary32).FADD .RNE 0x3F800000#32 0x40000000#32).1   -- 0x40400000#32 (3.0)

-- Read the rounding mode from the rm field of an instruction (111 = DYN) and frm (010 = RDN). none for a reserved value.
#eval RISCV.riscv.decode 7#3 2#3   -- some RDN
```

To check a file, use the editor (the Lean language server) or `lake build` / `lake lean <file>`.
`lake env lean <file>` does not work ([Known issues](#known-issues)).

**When requiring the verification side**

The verification side depends on Mathlib (the Mathlib version is pinned to the tag written in the lakefiles of this
repository). After `lake update`, run `lake exe cache get` to fetch the prebuilt Mathlib (the first time, fetching Mathlib
takes time and disk space). Run it before the first `lake build`: without the prebuilt Mathlib, `lake build` builds Mathlib
from source, which takes hours. If your project itself requires a different version of Mathlib, the resolution conflicts, so
align the versions.

## The groups of RISC-V instructions

The RISCV entry point for users is the value `riscv` of the RISC-V group of operations (`RiscvOps`). The fields of the value are
four functions that take a format (or a pair of formats) and return a group of instructions, the decoding of rm `decode`, the
per-format groups of functions `F16` to `F128`, and `toFflags`, which maps a set of flags to the value of fflags. Instructions
are called as fields of the groups of instructions.

| Group type (`SoftFloat.RISCV.Base`) | Value (field of `riscv` in `SoftFloat.RISCV.Operators`) | Instructions | Examples |
|---|---|---|---|
| `InstructionOps fmt` | `riscv.instructions fmt` | Scalar instructions of F, D, Q, Zfh and Zfa | FADD.S is `(riscv.instructions .binary32).FADD`, FCVT.W.D is `(riscv.instructions .binary64).FCVT_W_F`, FLI.H is `(riscv.instructions .binary16).FLI` |
| `ConversionOps src dst` | `riscv.conversions src dst` | Conversions between formats (including conversions to and from BF16) | FCVT.S.D is `(riscv.conversions .binary64 .binary32).FCVT`, FCVT.BF16.S is `(riscv.conversions .binary32 .bf16).FCVT` |
| `WideningOps narrow wide` | `riscv.widenings narrow wide` | Vector widening arithmetic, multiply-add, ordered widening reductions, VFWMACCBF16, and the narrowing conversion with round-to-odd (vfncvt.rod.f.f.w) | vfwadd with SEW=16 is `(riscv.widenings .binary16 .binary32).VFWADD`, VFWMACCBF16 is `(riscv.widenings .bf16 .binary32).VFWMACC`, vfncvt.rod.f.f.w with SEW=32 is `(riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W` |
| `VectorOps fmt` | `riscv.vectorOps fmt` | Vector element operations not among the scalar instructions (vfrec7, vfrsqrt7, vmfne, vmfgt, vmfge, conversions to and from integers, ordered reductions, min and max reductions) | vfrec7 with SEW=32 is `(riscv.vectorOps .binary32).VFREC7`, vfncvt.x.f.w with SEW=8 is `(riscv.vectorOps .binary16).VFNCVT_X_F_W` |

A field is named after its instruction, with `.` replaced by `_` and the format letters fixed by the arguments of the group
removed (FCVT.W.S is `FCVT_W_F`, FCVT.S.W is `FCVT_F_W`; `F` is the floating-point format of the group). Operands and results
are `BitVec`s of the width of the format, and the integers of conversions to and from integers are `BitVec 32` or `BitVec 64`.
Instructions that round and instructions that have an rm field take a rounding mode `RoundingMode` (`RNE`, `RTZ`, `RDN`, `RUP`,
`RMM`); instructions with a fixed rounding (`FCVTMOD_W_D` always rounds toward 0) do not. Instructions that can raise flags
return a pair of the result and `StatusFlags`; instructions that raise no flags (sign injection, `FCLASS`, `FLI`) return only the
result. FCVTMOD.W.D is an instruction of the D extension, so the claim states it only for binary64 (precondition
`InstructionDomain.FCVTMOD_W_D`).

The vector floating-point instructions of V and Zvfh (Chapter 31 of The RISC-V Instruction Set Manual, Volume I: Unprivileged
Architecture, version 20260120; "the RISC-V manual" below) have their element operations as fields of the groups.
Those whose element operation is the same as a scalar instruction (vfadd, vfsub, vfmul, vfdiv, vfsqrt, single-width
multiply-add, vfmin, vfmax, sign injection, vmfeq, vmflt, vmfle, vfclass, conversions with integers of width 32 and 64,
conversions between formats, and the BF16 conversions of Zvfbfmin) use the fields of the value of the scalar group of
instructions with the operands rearranged (for example, vd[i] = vs1[i] × vs2[i] + vd[i] of vfmacc is
`(riscv.instructions .binary32).FMADD rm vs1 vs2 vd`, and vfrsub is `(riscv.instructions .binary32).FSUB rm f vs2`). However,
since `VectorOps fmt` has the same fields for every format, the fields for conversions with integers in the binary32 and
binary64 groups (`(riscv.vectorOps .binary32).VFCVT_X_F_V`, `(riscv.vectorOps .binary64).VFNCVT_X_F_W`, and others) are in the
group as functions with the same meaning as the scalar conversions (`FCVT_W_F` and others), and the claim states their
correctness too. Either gives the same result. .vv and .vf have the same element operation, so they are one field. Vector
instructions use the dynamic rounding mode in frm, so the ISA model decodes frm with `riscv.decode` and passes it, and passes
`.RTZ` for the rtz variants. The reduction fields take the initial value (vs1[0]) and the sequence of active elements and fold
them in element order. The unordered reductions (vfredusum and vfwredusum) do not determine a single result, so they are not
in the groups; they are written as a relation in the specification (the set of permitted results `UnorderedSumOf`), and we
prove that the result of the ordered reduction satisfies it (the ISA model may use `VFREDOSUM` for vfredusum). The round-to-odd
vfncvt.rod.f.f.w is the field `VFNCVT_ROD_F_F_W` of the group of widening operations; its rounding is fixed to round-to-odd,
and it takes no rounding mode. Round-to-odd is the Core rounding direction `roundToOdd`; IEEE 754 does not define it, so its
meaning is set by the Core specification (`roundMagToOdd` in `SoftFloat.Core.Spec.Real` and the handling of overflow in
`SoftFloat.Core.Spec.Result`). The RISC-V rounding mode `RoundingMode` has no round-to-odd, so round-to-odd cannot be passed to
the functions of the other instructions.
The note in Section 31.13.19 of the RISC-V manual (making every step except the last of a sequence that narrows by halves a vfncvt.rod.f.f.w gives the same
result and flags as rounding once) is stated, for the sequence from binary64 to binary16, by the field
`narrowingInHalvingSteps` of the correctness predicate `RiscvCorrect`.

For each group, the RISCV specification has a correctness predicate (`InstructionCorrect` and others), a precondition
(`InstructionDomain`) and an agreement predicate (`InstructionAgree` and others). The formats and pairs of formats that RISC-V
has are definitions in the specification (`scalarFormats`, `conversionPairs`, `wideningPairs`, `vectorFormats`); on top of them,
the correctness predicate of the RISC-V group of operations `RiscvCorrect` bundles the correctness predicate of each group and
the properties of the decoding of rm, the per-format groups of functions, the bit order of fflags (NV, DZ, OF, UF, NX at bits
4 to 0, as in the fcsr layout of Figure 2 in Section 21.2 of the RISC-V manual), the meaning of the rounding modes, the unordered reductions, the min
and max reductions, and the sequences that narrow by halves; the agreement predicate `RiscvAgree` bundles, over the same range,
the agreement of each group, of the decoding of rm, and of the values of fflags. The claim (`SoftFloat.RISCV.Claim`) is two
theorems, like the Core claim ("Implementation-defined behavior" below).

```lean
theorem correctness : Spec.RiscvChoices Specialization.riscv ∧ Spec.RiscvCorrect Specialization.riscv riscv

theorem uniqueness :
    ∀ sp₁ sp₂ o₁ o₂, Spec.RiscvChoices sp₁ → Spec.RiscvChoices sp₂ →
      Spec.RiscvCorrect sp₁ o₁ → Spec.RiscvCorrect sp₂ o₂ → Spec.RiscvAgree o₁ o₂
```

`correctness` states that the value of the RISC-V specialization satisfies the RISC-V choices and that `riscv` satisfies the
correctness predicate under it; `uniqueness` states that two groups that each satisfy the correctness predicate under two
specializations satisfying the RISC-V choices agree (that is, the RISC-V choices and the predicates determine a single result).
The RISC-V choices (`RiscvChoices`) fix only the points that the RISC-V documents specify, and do not fix the points they leave
unspecified (such as the sign of the NaN that setPayload produces). Because `uniqueness` takes the two specializations
separately, the meaning of the correctness predicate does not change however those points are chosen, and the two theorems
together say that the instructions of `riscv` are exactly the meaning of the RISC-V instructions. The correspondence between the
fields of the groups and of the predicates is confirmed by checks inside the build of the specification (for each group,
`SoftFloat.RISCV.Spec.checkCoverage`; for the group that bundles them, `SoftFloat.RISCV.Spec.checkOperationsCoverage`).

The groups of instructions of `riscv` hold the meaning of instructions whose result bits and flags are determined by the input
bit strings (and the rounding mode), including the parts that are not IEEE 754 operations (sign injection, the variants of
multiply-add, the classification mask, the handling of NaN in minimum and maximum, the table of constants of `FLI`, the
wrapping modular conversion of `FCVTMOD.W.D`, and others). They do not hold the following, which are held by the ISA model
(sail-riscv and others).

- The encoding of instructions, and making an instruction illegal when the rm field decodes as invalid (the decoding itself is
  `riscv.decode`)
- Reading and writing registers (checking NaN-boxing, sign-extending 32-bit results to XLEN, and the bit moves of fmv, FMVH,
  FMVP, loads and stores)
- Which instructions exist when which extensions are implemented (the values can be built for any format regardless of the
  conditions, and the claim is stated for the RISC-V formats)
- Vector registers, masks, LMUL, vl, vstart and the per-element iteration, reading the scalar of .vf, which elements go into the
  sequence of a reduction, and zero-extending the result of vfclass to SEW
- The state of fcsr, frm and fflags (accumulating flags is `StatusFlags.union`, and the map to the bits of fflags is
  `riscv.toFflags`)

The per-format groups of functions (`riscv.F16` to `riscv.F128`) are groups of functions at the Core level. The groups of
instructions do not use them; they are used to compare the operations not in the groups of instructions (the signaling equality
comparison and round-to-odd) against TestFloat.

## Implementation-defined behavior

IEEE 754 leaves some behavior to the implementation. Core keeps those that the operations use as axes of the specialization
(`Specialization`) and does not choose their values. The Core correctness theorem states, for every valid specialization, the
correctness of both the group of operations `softfloat sp` and the per-format groups of functions built from it,
`perFormat (softfloat sp) fmt`. The value of the RISCV specialization (`Specialization.riscv`), the per-format functions that
use it (`riscv.F16` to `riscv.F128`), and the groups of instructions of `riscv` match these to RISC-V. The Core claim
(`SoftFloat.Core.Claim`) is two theorems:

```lean
theorem correctness :
    ∀ sp, Spec.Specialization.Valid sp →
      Spec.Correct sp (softfloat sp) ∧ ∀ fmt, Spec.FormatCorrect sp fmt (perFormat (softfloat sp) fmt)

theorem uniqueness :
    ∀ sp o₁ o₂, Spec.Specialization.Valid sp → Spec.Correct sp o₁ → Spec.Correct sp o₂ → Spec.Agree o₁ o₂
```

`correctness` states that, for every valid specialization, `softfloat sp` satisfies the correctness predicate and so does each
per-format group of functions built from it; `uniqueness` states that two groups of operations that satisfy the correctness
predicate under the same valid specialization agree.

What the Core claim states is that, except for the following points that Core fixes as its interpretation of IEEE 754, a
group of operations conforming to IEEE 754 satisfies the correctness predicate under the valid specialization whose axes take
the values it chose.

- setPayload and setPayloadSignaling do not read −0 as a non-negative floating-point integer (an interpretation of a sentence
  in 9.7 of IEEE 754-2019; the section numbers of IEEE 754 here are those of IEEE 754-2019 unless the 2008 edition is named).
- scaleB with x and N both NaN, when logBFormat is a floating-point format, follows NaN propagation (6.2) as the case where x is
  NaN.
- Handling of the two editions: in totalOrder, the order between NaNs of the same sign and kind follows the 2019 edition, which
  relaxed it to implementation-defined, rather than the order of payloads in the 2008 edition, and any total order is allowed as
  the value of the axis.

The following four are choices specified by the RISC-V documents, and are the same behavior as the RISCV specialization of
Berkeley SoftFloat (`SPECIALIZE_TYPE=RISCV`).

- Tininess is detected after rounding.
- fusedMultiplyAdd(0, ∞, c) and fusedMultiplyAdd(∞, 0, c) raise invalid even when c is a quiet NaN (IEEE 754 leaves it to the
  implementation whether to raise invalid in this case).
- Operations that return a NaN do not propagate the input NaN, and return the default quiet NaN (`0x7FC00000` for binary32).
- When a conversion from floating-point to integer is invalid, it returns a saturated value: the maximum for NaN and on the
  positive side, and the minimum on the negative side.

For the following points, RISC-V has no corresponding instruction and the RISC-V documents do not specify them, so we chose the
values of `Specialization.riscv`. They are not part of the RISC-V choices (`RiscvChoices`).

- The sign of the NaN that setPayload and setPayloadSignaling produce is positive. The accepted payloads are all non-negative
  integers that fit in the format (excluding 0 for setPayloadSignaling).
- In totalOrder, NaNs of the same sign and kind are ordered by payload. This is within the range of the 2019 edition and is
  exactly the order of 5.10 of the 2008 edition, so it conforms to both editions.
- In minNum, maxNum, minNumMag and maxNumMag of the 2008 edition, between −0 and +0, −0 is chosen as the smaller.
- scaleB with N NaN, when logBFormat is a floating-point format, returns the default quiet NaN, as for NaN inputs of the other
  operations.

Berkeley TestFloat, used in the comparison against TestFloat, also computes the expected values with SoftFloat built with
`SPECIALIZE_TYPE=RISCV`. The operations compared are the arithmetic, rounding to integral values (`-exact` and `-notexact`),
comparisons, conversions to and from integers and conversions between formats of the four formats, and the two conversions
between BF16 and binary32, 102 operations in all; each is compared in the five rounding modes, and the 101 operations other
than `bf16_to_f32` are also compared with round-to-odd (`testfloat_gen -rodd`) (level 1; the records are in
`riscv-verification/testfloat/records/`). Operations that correspond to RISC-V instructions are compared through the fields of
the value of the groups of instructions (rounding to integral values via FROUNDNX and FROUND, and the quiet comparisons via FLTQ
and FLEQ). Round-to-odd cannot be passed to the instruction fields, so it is compared by passing `.roundToOdd` to the per-format
functions, and the conversions from binary64 to binary32 and from binary32 to binary16 are compared through
`VFNCVT_ROD_F_F_W`. Instructions not in TestFloat (FMIN, FMAX, FMINM, FMAXM, FMSUB, FNMSUB, FNMADD, sign injection, FCLASS, FLI,
FCVTMOD.W.D, VFWMACCBF16, and the fields of the group of widening operations and of the group of vector operations) are shown by
proof alone.

## Correspondence with the standards

We keep a separate document that relates each clause of IEEE 754-2019 and of the RISC-V manual to the definitions and
theorems in this repository, with the decisions taken where the standards leave a choice. It quotes the text of the
standards, which is copyrighted, so it is not published. What you can check from this repository alone is the claim
theorems (replayed in the kernel by `make check`) and the comparison against Berkeley TestFloat (the records in
`riscv-verification/testfloat/records/`, rerun by `make testfloat`). Instructions that TestFloat does not cover (listed
above) are shown by proof alone.

## Known issues

### Modules across packages are not found on Lean's search path

The four packages place their modules under the same prefix `SoftFloat` (`SoftFloat.Core.Base.…` in core-operators,
`SoftFloat.RISCV.Operators.…` in riscv-operators, and so on). Lake looks up the owning package for each module, so the
packages build in this form. However, the way Lean itself searches its search path (`LEAN_PATH`, `LEAN_SRC_PATH`) treats the
first component of a module name as belonging to one package. `findWithExt` in `src/lean/Lean/Util/Path.lean` of v4.35.0 searches
only the first entry that has the top-level directory `SoftFloat/`, and does not move on to the next entry even if the module
file is not there. As a result, tools that look up modules on the search path cannot find the modules of the second and later
packages, and stop with an error such as the following (the path points inside core-operators, the first to have
`SoftFloat/`).

```
object file '…/core-operators/.lake/build/lib/lean/SoftFloat/RISCV/Operators.olean' of module SoftFloat.RISCV.Operators does not exist
```

Upstream, the language server failing to go to definitions for the same reason remains open as
[leanprover/lean4#4962](https://github.com/leanprover/lean4/issues/4962).

**Uses not affected**: `lake build`, `lake lean <file>`, elaboration in the editor (Lake passes the location of each module to
Lean directly), and `lake exe` (it only runs a built executable).

**Tools affected**:

- `lake env lean <file>` (anything that runs `lean` on a file without `--setup`)
- `lean --deps` and `lean --src-deps` (they silently print paths that do not exist)
- `leanchecker <module>`
- `leanexport <module>`
- `lake check` and `lake comparator`
- `lake lint` (the built-in lint)
- `lake shake`
- Anything in which the language server looks for source files, such as go-to-definition in the editor

**Workaround script**: `scripts/lean-env.sh <package directory> <command> [args…]` gathers, with symbolic links into a
single tree in a temporary directory (the tree of .olean files and the tree of sources are kept separate), the entries of the
package's search path (as set by `lake env`) that have `SoftFloat/`, puts them at the front of the search path, and runs the
command in the package's environment. The command runs in the directory it was called from, and the exit code is the
command's. If the same module is in two entries, it stops without choosing one (exit 125). The package directory may be a
package in this repository or a user's project that requires a package. Build first: in this repository with `make build`
("Building and checking" below), in a user's project with `lake build`.

```sh
# From the top of this repository
./scripts/lean-env.sh riscv-verification lean Try.lean
./scripts/lean-env.sh riscv-verification lean --deps Try.lean
./scripts/lean-env.sh riscv-verification leanchecker SoftFloat.RISCV.Claim
./scripts/lean-env.sh riscv-verification leanexport SoftFloat.RISCV.Claim >claim.export

# From the top of a user's project that requires softfloat-riscv-operators from git
.lake/packages/softfloat-riscv-operators/scripts/lean-env.sh . lean Main.lean
```

The paths under `SoftFloat/` that `lean --deps` and `--src-deps` print point into the tree in the temporary directory, and
disappear when the command finishes.

**Not avoidable**:

- `lake check`, `lake lint` and `lake shake` determine the search path themselves, so the `LEAN_PATH` that
  `scripts/lean-env.sh` sets has no effect. `lake check` can check what `leanexport` exported through `scripts/lean-env.sh`
  when it is passed with `--from-export` (it checks only what was exported and does not rebuild the project).

  ```sh
  ./scripts/lean-env.sh core-verification leanexport SoftFloat.Core.Claim \
      -- SoftFloat.Claim.correctness SoftFloat.Claim.uniqueness >claim.export
  (cd core-verification && lake check --from-export ../claim.export)
  ```

  `scripts/check-claim-build.sh` replays the claims, exported in the same way, in the kernel with `leanchecker --from-export`.
  There is no workaround for `lake lint` and `lake shake`.
- Anything in which the language server looks for source files, such as go-to-definition in the editor (upstream
  [leanprover/lean4#4962](https://github.com/leanprover/lean4/issues/4962)).

## Development guide

### Prerequisites

- Nix with flakes enabled ([Flakes](https://wiki.nixos.org/wiki/Flakes)).
- Network access the first time: elan fetches the Lean toolchain named in `lean-toolchain`, and `make deps` fetches Mathlib
  and its built files.
- Disk space: about 20 GB, measured with `du` after `make build` with Lean v4.35.0: about 16 GB in this repository (most of it the copy
  of Mathlib in `.lake/packages/` of each of the two packages of the verification, about 7 GB each), about 3 GB for the
  toolchain in `~/.elan/`, and about 0.5 GB for the downloaded files of Mathlib in `~/.cache/mathlib/`.

### Setting up the environment

The usual development environment starts with the following command:

```sh
nix develop          # or: direnv allow
```

If you need a strict development environment to ensure reproducibility,
run the following:

```sh
./scripts/restricted-devshell.sh
```

### Building and checking

Build and check through the `Makefile` (GNU make; the devshell provides it), from the top of this repository:

```sh
make deps        # fetch the built Mathlib for core-verification/ and riscv-verification/ (lake exe cache get)
make build       # deps, then lake build in the four packages in the order of their requirements
make check       # build, then the three checks below
make testfloat   # build, then run the comparison with TestFloat again and rewrite its record
make help        # the list of targets (also clean)
```

In the strict development environment, run them through it (`./scripts/restricted-devshell.sh make check`).

`make deps` fetches the built Mathlib once for each revision of Mathlib in the `lake-manifest.json` of the two packages of
the verification, and stops if `Mathlib.olean` is not there afterwards. Running `lake build` directly in a package of the
verification before that can build Mathlib from source, which takes hours; the scripts that build (`scripts/check-*.sh`
and the scripts of the comparison) stop and ask for `make deps` when the built Mathlib is missing. The targets that build
hold the lock `.lake-build.lock`, so two builds in the same tree do not overlap: the second one waits for the first.

`make check` runs the following scripts, and stops at the first that fails. Each writes its verdict as YAML to standard
output and returns the result as its exit code (see each script's `--help` for details).

- `scripts/check-claim-build.sh` — Builds the two packages on the verification side. The build includes the check that the
  statements of the claim theorems use only definitions of the permitted layers and the Lean core (`checkClaimStatements`),
  the check that the claim theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (`checkClaimAxioms`), and the
  check of the correspondence between the fields of the groups of operations and of the correctness and agreement predicates
  (`checkCoverage` and others). It then exports the two claim theorems and all the constants they depend on with `leanexport`,
  and replays them in the kernel from an empty environment with `leanchecker --from-export` (`status: built`,
  `kernel_replay: accepted`).
- `scripts/check-package-dependencies.sh` — Checks that the `require`s of the packages and the `import`s of the built modules go
  only in the permitted directions. The rules of the directions are written in `scripts/package-dependencies.yaml`.
- `scripts/check-testfloat-record.sh` — Checks that the records of the comparison against TestFloat
  (`riscv-verification/testfloat/records/`) were taken from the current sources, have all the rows of the comparison table, and
  all matched. The comparison itself is run by `make testfloat`
  (`riscv-verification/testfloat/scripts/record_testfloat_level1.sh`; it takes about 20 minutes), which rewrites the records.

The three version checks are not part of `make check`; run them alone, from the top of this repository in the devshell (they
read the network). `scripts/check-lean-versions.sh`, `scripts/check-mathlib-version.sh` and `scripts/check-nixpkgs-channel.sh`
check that the versions of the Lean toolchain, Mathlib and nixpkgs are each at their latest stable release.

The scripts of `make check` can also be run alone, after `make build`. A script run alone does not take the lock, so do not
run it while another build in the same tree is running.

## License

Copyright (c) 2026 Kazutaka Nakamura

The Lean code (the four packages) and the scripts are provided under the [Apache License 2.0](LICENSE).
