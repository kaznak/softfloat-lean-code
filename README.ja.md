# SoftFloatLean

[English](README.md) | [日本語](README.ja.md)

[Lean](https://lean-lang.org/) による [IEEE 754](https://standards.ieee.org/ieee/754/6210/) 二進浮動小数点演算。

## パッケージ

このリポジトリは、対象（Core・RISCV）ごとに、演算の側と検証の側の 2 つのパッケージを含みます。Core は対象によらず
各対象が特殊化して使う部分、RISCV は RISC-V の特殊化と命令の組です。モジュールの名前は
`SoftFloat.<対象>.<層>.…` です。

| パッケージ名 | ディレクトリ | 層（モジュールの頭） | 内容 | Mathlib |
|---|---|---|---|---|
| softfloat-core-operators | `core-operators/` | 基盤（`SoftFloat.Core.Base`）・演算（`SoftFloat.Core.Operators`） | 仕様と演算が共有する語彙（形式とそのパラメタ、符号化の分解と組み立て、丸め方向（IEEE 754 の 5 つの丸め方向属性と奇数への丸め）、フラグ、演算の一覧と型 `Ops`、形式ごとの関数の組の型 `FormatOps`）と、実行可能な IEEE 754 演算の実装（特殊化を引数に取る `softfloat sp`、形式ごとの関数の組を作る `perFormat`）。 | 不要 |
| softfloat-core-verification | `core-verification/` | 仕様（`SoftFloat.Core.Spec`）・証明（`SoftFloat.Core.Proof`）・主張（`SoftFloat.Core.Claim`） | 実装が正しいとはどういうことかを実数（`ℝ`）の値と丸めで述べた定義（`Correct`・`FormatCorrect` など）、その証明、最終的に証明される定理（`SoftFloat.Claim.correctness`・`SoftFloat.Claim.uniqueness`）。 | 必要 |
| softfloat-riscv-operators | `riscv-operators/` | 基盤（`SoftFloat.RISCV.Base`）・演算（`SoftFloat.RISCV.Operators`） | 基盤は、仕様と演算が共有する RISC-V の語彙で、4 つの命令の組の型（スカラの命令の `InstructionOps fmt`、形式の間の変換の `ConversionOps src dst`、ベクタの拡幅の演算の `WideningOps narrow wide`、スカラの命令に無いベクタの要素の演算の `VectorOps fmt`）と、それらと rm の読み替えと形式ごとの関数の組と fflags のビットへの写しを 1 つにまとめた RISC-V の演算の組の型（`RiscvOps`）、丸めモード（`RoundingMode`）、BF16 の形式（`Format.bf16`）。演算は、その RISC-V の値 `riscv`（利用者の入口で、命令は値のフィールドの組のフィールド `(riscv.instructions .binary32).FADD`・`(riscv.conversions .binary64 .binary32).FCVT` などとして呼び、rm の欄と frm からの読み替えは `riscv.decode`、`BitVec` 上の形式ごとの関数の組は `riscv.F16`〜`riscv.F128`、フラグの組から fflags の値への写しは `riscv.toFflags`）と、その下の RISC-V の特殊化の値（`Specialization.riscv`）。結果はビットパターンまで一致。 | 不要 |
| softfloat-riscv-verification | `riscv-verification/` | 仕様（`SoftFloat.RISCV.Spec`）・証明（`SoftFloat.RISCV.Proof`）・主張（`SoftFloat.RISCV.Claim`）・照合（`SoftFloat.RISCV.Test`） | RISC-V の選択の述語（`RiscvChoices`）、RISC-V にある形式と形式の組、命令の組ごとの正しさ・前提・一致の述語（`InstructionCorrect`・`InstructionAgree` など）とそれを束ねる RISC-V の演算の組の正しさ・一致の述語（`RiscvCorrect`・`RiscvAgree`）と対応の検査、その証明、最終的に証明される定理（`SoftFloat.RISCV.Claim.correctness`・`SoftFloat.RISCV.Claim.uniqueness`）、Berkeley TestFloat（IEEE 754 適合性の検査器）との差分照合（`testfloat/`）。 | 必要 |

- パッケージの依存の向きは、`core-operators/` ← `core-verification/`、`core-operators/` ← `riscv-operators/`、
  `riscv-operators/` と `core-verification/` ← `riscv-verification/` です。演算の側は検証の側と Mathlib に依らず、Core は
  RISCV に依りません。
- 層の向きは、対象の中で、基盤 ← 演算、基盤 ← 仕様、仕様と演算 ← 証明 ← 主張です（仕様は演算と証明に依りません）。
  RISCV の層は Core の同じ層とそれより下の層に依ってよく、照合は RISCV の演算だけに依ります。検証の側の中の向きは
  Lake では保てないので、`scripts/check-package-dependencies.sh` がモジュールの import から確かめます。
- 正しさのために読むのは、両方の対象の基盤と仕様の全体と、両方の主張の定理の文です。演算・証明・照合は、Lean の証明と
  照合の結果に任せます。
- 利用者は、演算の側のパッケージを `require` し、`import SoftFloat.Core.Operators`（Core の演算と基盤の語彙）か
  `import SoftFloat.RISCV.Operators`（RISC-V の値 `riscv` まで）と書きます。演算の側は Mathlib に依らないので、
  Mathlib は付いてきません。

### require のしかた

利用者のプロジェクトの lakefile から、使いたい部分のパッケージを 1 つ `require` します。パッケージはリポジトリの直下の
ディレクトリにあるので、git で `require` するときは `subDir` にそのディレクトリを書きます。

**どれを require するか**

| 使いたいもの | require するパッケージ（`name`） | `subDir` | import | Mathlib |
|---|---|---|---|---|
| 特殊化を自分で選んで、形式について一般の演算（`softfloat sp`）を使う | softfloat-core-operators | `core-operators` | `import SoftFloat.Core.Operators` | 不要 |
| RISC-V の命令（`(SoftFloat.RISCV.riscv.instructions .binary32).FADD` など）を使う | softfloat-riscv-operators | `riscv-operators` | `import SoftFloat.RISCV.Operators` | 不要 |
| Core の仕様と定理（`SoftFloat.Spec.Correct`・`SoftFloat.Claim.correctness` など）を使う | softfloat-core-verification | `core-verification` | `import SoftFloat.Core.Spec`・`import SoftFloat.Core.Claim` など | 必要 |
| RISC-V の仕様と定理（`RiscvChoices`・`RiscvCorrect`・`SoftFloat.RISCV.Claim.correctness` など）を使う | softfloat-riscv-verification | `riscv-verification` | `import SoftFloat.RISCV.Spec.Agree`（`RiscvChoices`・`RiscvCorrect`・`RiscvAgree` まで）・`import SoftFloat.RISCV.Claim` など | 必要 |

パッケージは、自分が require するパッケージ（その `lakefile.toml` の `[[require]]`。向きは上の「パッケージ」のとおり）を、
同じリポジトリの中から自動で取り込みます。softfloat-riscv-operators と softfloat-core-verification はどちらも
softfloat-core-operators を取り込み、softfloat-riscv-verification は softfloat-riscv-operators と softfloat-core-verification
（とそれらを通して softfloat-core-operators）を取り込みます。たとえば `import SoftFloat.RISCV.Operators` で Core の演算と基盤の
語彙まで使えます。**require するほかのパッケージが取り込むパッケージは、require しません。** 両方を require すると、同じ
リポジトリを 2 回取得し、さらに別々の `rev` を書くと、取り込む側のパッケージは利用者が直接書いた方を使って、警告なしに版が
食い違います。両方を書く必要があるときは、同じ `rev` を書きます。

**lakefile.toml の書き方**（`git` と `rev` は、このリポジトリの URL と、使う commit か tag に置き換えます）

```toml
[[require]]
name = "softfloat-riscv-operators"
git = "<このリポジトリの URL>"
rev = "<commit か tag>"
subDir = "riscv-operators"
```

**lakefile.lean の書き方**

```lean
require «softfloat-riscv-operators» from git
  "<このリポジトリの URL>" @ "<commit か tag>" / "riscv-operators"
```

**使い方の例**

```lean
import SoftFloat.RISCV.Operators

open SoftFloat

-- FADD.S: 1.0 + 2.0（丸めモード RNE）。結果のビットとフラグの組を返す。
#eval ((RISCV.riscv.instructions .binary32).FADD .RNE 0x3F800000#32 0x40000000#32).1   -- 0x40400000#32（3.0）

-- 命令の rm の欄（111 = DYN）と frm（010 = RDN）から丸めモードを読む。予約の値なら none。
#eval RISCV.riscv.decode 7#3 2#3   -- some RDN
```

ファイルを確かめるときは、エディタ（Lean の言語サーバ）か `lake build`・`lake lean <ファイル>` を使います。
`lake env lean <ファイル>` は使えません（[既知の問題](#既知の問題)）。

**検証の側を require するとき**

検証の側は Mathlib に依ります（Mathlib の版は、このリポジトリの lakefile に書いた tag に固定しています）。`lake update` の
後に、組み済みの Mathlib を取得するには `lake exe cache get` を実行します（初回は Mathlib の取得に時間とディスクを使います）。
最初の `lake build` の前に実行します。組み済みの Mathlib が無いと、`lake build` は Mathlib をソースから組み、何時間もかかります。
利用者のプロジェクト自身が別の版の Mathlib を require していると、解決が食い違うので、版をそろえてください。

## RISC-V の命令の組

RISCV の利用者の入口は、RISC-V の演算の組（`RiscvOps`）の値 `riscv` です。値のフィールドは、形式（か形式の組）を受けて命令の組を
返す 4 つの関数と、rm の読み替え `decode`、形式ごとの関数の組 `F16`〜`F128`、フラグの組を fflags の値に写す `toFflags` です。命令は、命令の組のフィールドとして呼びます。

| 組の型（`SoftFloat.RISCV.Base`） | 値（`SoftFloat.RISCV.Operators` の `riscv` のフィールド） | 命令 | 例 |
|---|---|---|---|
| `InstructionOps fmt` | `riscv.instructions fmt` | F・D・Q・Zfh と Zfa のスカラの命令 | FADD.S は `(riscv.instructions .binary32).FADD`、FCVT.W.D は `(riscv.instructions .binary64).FCVT_W_F`、FLI.H は `(riscv.instructions .binary16).FLI` |
| `ConversionOps src dst` | `riscv.conversions src dst` | 形式の間の変換（BF16 との変換を含む） | FCVT.S.D は `(riscv.conversions .binary64 .binary32).FCVT`、FCVT.BF16.S は `(riscv.conversions .binary32 .bf16).FCVT` |
| `WideningOps narrow wide` | `riscv.widenings narrow wide` | ベクタの拡幅の算術・積和・順に足す拡幅の縮約、VFWMACCBF16、奇数への丸めの縮幅の変換（vfncvt.rod.f.f.w） | SEW=16 の vfwadd は `(riscv.widenings .binary16 .binary32).VFWADD`、VFWMACCBF16 は `(riscv.widenings .bf16 .binary32).VFWMACC`、SEW=32 の vfncvt.rod.f.f.w は `(riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W` |
| `VectorOps fmt` | `riscv.vectorOps fmt` | スカラの命令に無いベクタの要素の演算（vfrec7・vfrsqrt7・vmfne・vmfgt・vmfge・整数との変換・順に足す縮約・min と max の縮約） | SEW=32 の vfrec7 は `(riscv.vectorOps .binary32).VFREC7`、SEW=8 の vfncvt.x.f.w は `(riscv.vectorOps .binary16).VFNCVT_X_F_W` |

フィールドの名前は命令の名前で、`.` を `_` にし、組の引数が決める形式の文字は外します（FCVT.W.S は `FCVT_W_F`、FCVT.S.W は
`FCVT_F_W`。`F` は組の浮動小数点の形式）。オペランドと結果は形式の幅の `BitVec`、整数との変換の整数は `BitVec 32` か
`BitVec 64` です。丸めを行う命令と rm の欄を持つ命令は丸めモード `RoundingMode`（`RNE`・`RTZ`・`RDN`・`RUP`・`RMM`）を受け、丸めを
固定する命令（`FCVTMOD_W_D` は常に 0 に向けて丸める）は受けません。フラグを立てうる命令は結果と `StatusFlags` の組を返し、フラグを
立てない命令（符号注入・`FCLASS`・`FLI`）は結果だけを返します。FCVTMOD.W.D は D 拡張の命令なので、主張は binary64 についてだけ
述べます（前提 `InstructionDomain.FCVTMOD_W_D`）。

V・Zvfh のベクタの浮動小数点の命令（The RISC-V Instruction Set Manual, Volume I: Unprivileged Architecture の版 20260120
の第 31 章。以下「RISC-V のマニュアル」）は、要素ごとの演算を組のフィールドとして持ちます。要素の演算がスカラの命令と同じもの
（vfadd・vfsub・vfmul・vfdiv・vfsqrt・単一幅の積和・vfmin・vfmax・符号注入・vmfeq・vmflt・vmfle・vfclass・整数の幅が 32・64 の
変換・形式の間の変換・Zvfbfmin の BF16 の変換）は、スカラの命令の組の値のフィールドをオペランドを並べ替えて使います（たとえば
vfmacc の vd[i] = vs1[i] × vs2[i] + vd[i] は `(riscv.instructions .binary32).FMADD rm vs1 vs2 vd`、vfrsub は
`(riscv.instructions .binary32).FSUB rm f vs2`）。ただし、`VectorOps fmt` はどの形式でも同じフィールドを持つので、binary32・binary64 の組の
整数との変換のフィールド（`(riscv.vectorOps .binary32).VFCVT_X_F_V`・`(riscv.vectorOps .binary64).VFNCVT_X_F_W` など）は、スカラの変換
（`FCVT_W_F` など）と同じ意味の関数として組にあり、主張はその正しさも述べます。どちらを使っても結果は同じです。.vv と .vf は要素の演算が同じなので 1 つのフィールドです。ベクタの命令は frm の動的な
丸めモードを使うので、ISA のモデルは frm を `riscv.decode` で読み替えて渡し、rtz の変種には `.RTZ` を渡します。縮約の
フィールドは、初期値（vs1[0]）と有効な要素の並びを受けて要素の順に畳み込みます。順序を決めない縮約（vfredusum・vfwredusum）は
結果が 1 つに決まらないので組に入れず、仕様の関係（許される結果の集合 `UnorderedSumOf`）として書き、順に足す縮約の結果がそれを
満たすことを証明しています（ISA のモデルは vfredusum に `VFREDOSUM` を使えます）。奇数への丸めの vfncvt.rod.f.f.w は、拡幅の演算の
組のフィールド `VFNCVT_ROD_F_F_W` で、丸めは奇数への丸めに固定され、丸めモードを受けません。奇数への丸めは Core の丸め方向
`roundToOdd` で、IEEE 754 に定義は無いので、その意味は Core の仕様（`SoftFloat.Core.Spec.Real` の `roundMagToOdd` と、
`SoftFloat.Core.Spec.Result` の溢れの扱い）が定めます。RISC-V の丸めモード `RoundingMode` には奇数への丸めが無いので、ほかの命令の関数に奇数への丸めを渡すことはできません。
RISC-V のマニュアルの 31.13.19 節の注記（半分ずつ狭める列の最後の段のほかを vfncvt.rod.f.f.w にすれば、一度に丸めたのと同じ結果とフラグになる）は、
binary64 から binary16 への列について、正しさの述語 `RiscvCorrect` のフィールド `narrowingInHalvingSteps` が述べます。

各組には、RISCV の仕様に正しさの述語（`InstructionCorrect` など）・前提（`InstructionDomain`）・一致の述語（`InstructionAgree` など）が
あります。RISC-V にある形式と形式の組は仕様の定義（`scalarFormats`・`conversionPairs`・`wideningPairs`・`vectorFormats`）で、RISC-V の
演算の組の正しさの述語 `RiscvCorrect` が、その上で各組の正しさの述語と、rm の読み替え・形式ごとの関数の組・fflags のビットの並び
（RISC-V のマニュアルの 21.2 節の図 2 の fcsr の並びのとおり NV・DZ・OF・UF・NX がビット 4〜0）・丸めモードの意味・順序を決めない縮約・min と max の縮約・半分ずつ狭める
列の性質を束ね、一致の述語 `RiscvAgree` が同じ範囲で各組と rm の読み替えと fflags の値の一致を束ねます。主張（`SoftFloat.RISCV.Claim`）は、Core の主張（下の「実装に委ねられた振る舞い」）と同じく 2 つの定理です。

```lean
theorem correctness : Spec.RiscvChoices Specialization.riscv ∧ Spec.RiscvCorrect Specialization.riscv riscv

theorem uniqueness :
    ∀ sp₁ sp₂ o₁ o₂, Spec.RiscvChoices sp₁ → Spec.RiscvChoices sp₂ →
      Spec.RiscvCorrect sp₁ o₁ → Spec.RiscvCorrect sp₂ o₂ → Spec.RiscvAgree o₁ o₂
```

`correctness` は、RISC-V の特殊化の値が RISC-V の選択を満たし、`riscv` がその下で正しさの述語を満たすことを、`uniqueness` は、RISC-V の
選択を満たす 2 つの特殊化の下でそれぞれ正しさの述語を満たす 2 つの組が一致すること（RISC-V の選択と述語が結果を 1 つに決めていること）を
述べます。RISC-V の選択（`RiscvChoices`）は、RISC-V の文書が定める点だけを固定し、文書が定めない点（setPayload が作る NaN の符号など）は
固定しません。`uniqueness` は 2 つの特殊化を別に取るので、それらの点をどう選んでも正しさの述語の意味は変わらず、2 つの定理を合わせると、
`riscv` の命令は RISC-V の命令の意味そのものです。組と述語のフィールドの対応は、仕様のビルドの中の
検査（各組は `SoftFloat.RISCV.Spec.checkCoverage`、それを束ねる組は `SoftFloat.RISCV.Spec.checkOperationsCoverage`）が確かめます。

入力のビット列（と丸めモード）から結果のビット列とフラグが決まる命令の意味は、IEEE 754 の演算に当たらない部分（符号注入・
積和の変種・分類のマスク・最小と最大の NaN の扱い・`FLI` の定数の表・`FCVTMOD.W.D` の剰余で包む変換など）も含めて、`riscv` の
命令の組が持ちます。次のものは持たず、ISA のモデル
（sail-riscv など）が持ちます。

- 命令の符号化と、rm の欄を無効と読んだときに不正な命令にすること（読み替えそのものは `riscv.decode`）
- レジスタの読み書き（NaN-boxing の確かめ、32 ビットの結果の XLEN への符号拡張、fmv・FMVH・FMVP・ロード・ストアのビットの
  移動）
- どの拡張を実装したときにどの命令があるか（値は条件によらずどの形式にも作れ、主張は RISC-V の形式で述べます）
- ベクタのレジスタ・マスク・LMUL・vl・vstart と要素ごとの繰り返し、.vf のスカラの読み出し、どの要素を縮約の並びに入れるか、
  vfclass の結果の SEW への 0 の拡張
- fcsr・frm・fflags の状態（フラグの積み上げは `StatusFlags.union`、fflags のビットへの写しは `riscv.toFflags`）

形式ごとの関数の組（`riscv.F16` から `riscv.F128`）は、Core の水準の関数の組です。命令の組はこれを使わず、命令の組に無い演算
（signaling な等しさの比較と奇数への丸め）を TestFloat と照合するのに使います。

## 実装に委ねられた振る舞い

IEEE 754 は一部の振る舞いを実装に委ねています。Core はこれらのうち演算が使うものを特殊化（`Specialization`）の軸として持ち、
値を選びません。Core の正しさの定理は、妥当な特殊化のすべてについて、演算の組 `softfloat sp` と、それから作る形式ごとの関数の組
`perFormat (softfloat sp) fmt` の両方の正しさを述べます。RISCV の特殊化の値（`Specialization.riscv`）と、それを使う形式ごとの関数
（`riscv.F16` から `riscv.F128`）と `riscv` の命令の組は、これらを RISC-V に合わせます。Core の主張（`SoftFloat.Core.Claim`）は
2 つの定理です。

```lean
theorem correctness :
    ∀ sp, Spec.Specialization.Valid sp →
      Spec.Correct sp (softfloat sp) ∧ ∀ fmt, Spec.FormatCorrect sp fmt (perFormat (softfloat sp) fmt)

theorem uniqueness :
    ∀ sp o₁ o₂, Spec.Specialization.Valid sp → Spec.Correct sp o₁ → Spec.Correct sp o₂ → Spec.Agree o₁ o₂
```

`correctness` は、妥当な特殊化のすべてについて、`softfloat sp` と、それから作る形式ごとの関数の組のそれぞれが正しさの述語を
満たすことを、`uniqueness` は、同じ妥当な特殊化の下で正しさの述語を満たす 2 つの演算の組が一致することを述べます。

Core の主張が述べるのは、Core が IEEE 754 の解釈として固定する次の点を除き、IEEE 754 に適合する演算の組がそれの選んだ値を軸に
持つ妥当な特殊化の下で正しさの述語を満たす、ということです。

- setPayload・setPayloadSignaling は、−0 を負でない浮動小数点の整数と読みません（IEEE 754-2019 の 9.7 節の文の解釈。ここでの IEEE 754 の節番号は、2008 年版と書かない限り IEEE 754-2019 のもの）。
- logBFormat が浮動小数点の形式で x と N がどちらも NaN の scaleB は、x が NaN の場合として NaN の伝え方（6.2 節）に従います。
- 2 つの版の扱い: totalOrder で符号も種類も同じ NaN どうしの順序は、2008 年版の payload の大小でなく、それを
  implementation-defined に緩めた 2019 年版に従い、任意の全順序を軸の値に許します。

次の 4 つは RISC-V の文書が定める選択で、
Berkeley SoftFloat の RISCV specialization（`SPECIALIZE_TYPE=RISCV`）と同じ振る舞いです。

- tininess は丸めの後で検出します。
- fusedMultiplyAdd(0, ∞, c) と fusedMultiplyAdd(∞, 0, c) は、c が quiet NaN でも invalid を立てます（IEEE 754 はこの場合に
  invalid を立てるかを実装に委ねています）。
- NaN を返す演算は、入力の NaN を伝えず、既定の quiet NaN（binary32 なら `0x7FC00000`）を返します。
- 浮動小数点から整数への変換が invalid になるときは、飽和した値を返します。NaN と正の側は最大値、負の側は最小値です。

次の点は、RISC-V に当たる命令が無く、RISC-V の文書が定めないので、`Specialization.riscv` の値を我々が選んでいます。
RISC-V の選択（`RiscvChoices`）には入りません。

- setPayload・setPayloadSignaling が作る NaN の符号は正です。受け付ける payload は、形式に収まる負でない整数のすべて
  （setPayloadSignaling では 0 を除く）です。
- totalOrder で符号も種類も同じ NaN どうしは、payload の大小で順序付けます。2019 年版の範囲に入り、2008 年版の 5.10 節の
  順序そのものでもあるので、両方の版に適合します。
- 2008 年版の minNum・maxNum・minNumMag・maxNumMag で、−0 と +0 では −0 を小さいとして選びます。
- logBFormat が浮動小数点の形式で N が NaN の scaleB は、ほかの演算の NaN の入力と同じく既定の quiet NaN を返します。

TestFloat との照合で使う Berkeley TestFloat も、SoftFloat を `SPECIALIZE_TYPE=RISCV` でビルドしたもので期待値を計算します。
照合する演算は、4 つの形式の算術・整数の値への丸め（`-exact` と `-notexact`）・比較・整数との変換・形式の間の変換と、BF16 と
binary32 の間の 2 つの変換の、あわせて 102 演算で、それぞれを 5 つの丸めモードで照合し、さらに `bf16_to_f32` を除く 101 演算を
奇数への丸め（`testfloat_gen -rodd`）で照合します（level 1。記録は `riscv-verification/testfloat/records/`）。RISC-V の命令にあたる演算は
命令の組の値のフィールドで照合します（整数の値への丸めは FROUNDNX と FROUND、quiet な比較は FLTQ と FLEQ）。奇数への丸めは命令の
フィールドに渡せないので、形式ごとの関数に `.roundToOdd` を渡して照合し、binary64 から binary32 と binary32 から binary16 への変換は
`VFNCVT_ROD_F_F_W` で照合します。TestFloat に無い命令（FMIN・FMAX・FMINM・FMAXM・FMSUB・FNMSUB・FNMADD・符号注入・
FCLASS・FLI・FCVTMOD.W.D・VFWMACCBF16 と、拡幅の演算の組とベクタの演算の組のフィールド）は、証明だけで示します。

## 規格との対応

IEEE 754-2019 と RISC-V のマニュアルの各条項を、このリポジトリの定義と定理に対応させ、規格が選択を残すところの決定を記した
文書を、別に持っています。著作権のある規格の本文を引用するため、公開していません。このリポジトリだけで確かめられるのは、
主張の定理（`make check` でカーネルに再生）と、Berkeley TestFloat との照合（記録は `riscv-verification/testfloat/records/`、
やり直しは `make testfloat`）です。TestFloat に無い命令（上の一覧）は、証明だけで示しています。

## 既知の問題

### パッケージをまたぐモジュールが、Lean の検索の道で見つからない

4 つのパッケージは、モジュールを同じ頭 `SoftFloat` の下に置きます（`SoftFloat.Core.Base.…` は core-operators、
`SoftFloat.RISCV.Operators.…` は riscv-operators、など）。Lake はモジュールごとに持ち主のパッケージを引くので、この形で
組めます。しかし Lean 本体の検索の道（`LEAN_PATH`・`LEAN_SRC_PATH`）の探し方は、モジュールの名前の頭を 1 つのパッケージと
みなします。v4.35.0 の `src/lean/Lean/Util/Path.lean` の `findWithExt` は、入口のうち頭のディレクトリ `SoftFloat/` を持つ
最初の 1 つだけを探し、そこにモジュールのファイルが無くても次の入口へ進みません。そのため、検索の道でモジュールを探す道具は、
2 つ目以降のパッケージのモジュールを見つけられず、たとえば次のエラーで止まります（パスは `SoftFloat/` を最初に持つ
core-operators の中を指します）。

```
object file '…/core-operators/.lake/build/lib/lean/SoftFloat/RISCV/Operators.olean' of module SoftFloat.RISCV.Operators does not exist
```

上流では、同じ原因で言語サーバが定義への移動に失敗する件が
[leanprover/lean4#4962](https://github.com/leanprover/lean4/issues/4962) として開いたままです。

**影響しない使い方**: `lake build`、`lake lean <ファイル>`、エディタでの elaboration（Lake がモジュールごとの置き場を Lean に
直接渡します）、`lake exe`（組んだ実行ファイルを走らせるだけです）。

**影響する道具**:

- `lake env lean <ファイル>`（`lean` を `--setup` なしにファイルに対して走らせるもの全般）
- `lean --deps`・`lean --src-deps`（存在しないパスを黙って出します）
- `leanchecker <モジュール>`
- `leanexport <モジュール>`
- `lake check`・`lake comparator`
- `lake lint`（組み込みの lint）
- `lake shake`
- エディタの定義への移動など、言語サーバがソースのファイルを探すもの

**回避のスクリプト**: `scripts/lean-env.sh <パッケージのディレクトリ> <命令> [引数…]` は、そのパッケージの検索の道
（`lake env` が設定するもの）のうち `SoftFloat/` を持つ入口を、一時ディレクトリの 1 つの木にシンボリックリンクで集め
（.olean の木とソースの木を分けます）、検索の道の先頭に置いて、命令をパッケージの環境で走らせます。命令は呼び出した
ディレクトリで走り、終了コードは命令のものです。同じモジュールが 2 つの入口にあれば、片方を選ばずに止まります（終了 125）。
パッケージのディレクトリは、このリポジトリの中のパッケージでも、パッケージを require した利用者のプロジェクトでも構いません。
先に組んでおきます。このリポジトリでは `make build`（下の「組み方と検査」）、利用者のプロジェクトでは `lake build` で組みます。

```sh
# このリポジトリの直下から
./scripts/lean-env.sh riscv-verification lean Try.lean
./scripts/lean-env.sh riscv-verification lean --deps Try.lean
./scripts/lean-env.sh riscv-verification leanchecker SoftFloat.RISCV.Claim
./scripts/lean-env.sh riscv-verification leanexport SoftFloat.RISCV.Claim >claim.export

# git で softfloat-riscv-operators を require した利用者のプロジェクトの直下から
.lake/packages/softfloat-riscv-operators/scripts/lean-env.sh . lean Main.lean
```

`lean --deps`・`--src-deps` が出す `SoftFloat/` の下のパスは一時ディレクトリの木の中を指し、命令が終わると消えます。

**回避できないもの**:

- `lake check`・`lake lint`・`lake shake` は、検索の道を自分で決めるので、`scripts/lean-env.sh` が
  設定した `LEAN_PATH` は効きません。`lake check` は、`scripts/lean-env.sh` で `leanexport` に書き出させたものを
  `--from-export` で渡せば検査できます（書き出したものだけを検査し、プロジェクトを組み直しはしません）。

  ```sh
  ./scripts/lean-env.sh core-verification leanexport SoftFloat.Core.Claim \
      -- SoftFloat.Claim.correctness SoftFloat.Claim.uniqueness >claim.export
  (cd core-verification && lake check --from-export ../claim.export)
  ```

  `scripts/check-claim-build.sh` は、同じ形で書き出した主張を `leanchecker --from-export` でカーネルに再生します。
  `lake lint` と `lake shake` には回避の手がありません。
- エディタの定義への移動など、言語サーバがソースのファイルを探すもの（上流の
  [leanprover/lean4#4962](https://github.com/leanprover/lean4/issues/4962)）。

## 開発の手引

### 前提

- flakes を有効にした Nix（[Flakes](https://wiki.nixos.org/wiki/Flakes)）。
- 初回はネットワーク。elan が `lean-toolchain` に書いた Lean のツールチェインを取得し、`make deps` が Mathlib とその組み済みの
  ファイルを取得します。
- ディスク: `make build` の後に `du` で測ると、Lean v4.35.0 で約 20 GB です。このリポジトリに約 16 GB（大半は、検証の側の
  2 つのパッケージのそれぞれの `.lake/packages/` にある Mathlib の写しで、1 つ約 7 GB）、`~/.elan/` のツールチェインに約 3 GB、
  `~/.cache/mathlib/` の Mathlib の取得したファイルに約 0.5 GB です。

### 環境構築

通常の開発環境は以下のコマンドで立ち上がります:

```sh
nix develop          # または: direnv allow
```

再現可能性の担保のため厳密な開発環境が必要な場合は、
以下を実行してください:

```sh
./scripts/restricted-devshell.sh
```

### 組み方と検査

組むのも検査するのも、このリポジトリの直下から `Makefile`（GNU make。devshell にあります）で行います。

```sh
make deps        # core-verification/ と riscv-verification/ に組み済みの Mathlib を取得する（lake exe cache get）
make build       # deps の後、4 つのパッケージを依存の順に lake build する
make check       # build の後、下の 3 つの検査を回す
make testfloat   # build の後、TestFloat との照合を走らせ直して記録を書き直す
make help        # 目標の一覧（ほかに clean）
```

厳密な開発環境では、その中で回します（`./scripts/restricted-devshell.sh make check`）。

`make deps` は、検証の側の 2 つのパッケージの `lake-manifest.json` にある Mathlib の版ごとに 1 度だけ組み済みの Mathlib を
取得し、取得の後に `Mathlib.olean` が無ければ止まります。その前に検証の側のパッケージで直接 `lake build` を走らせると、
Mathlib をソースから組むことがあり、何時間もかかります。組む検査のスクリプト（`scripts/check-*.sh` と照合のスクリプト）は、
組み済みの Mathlib が無いときは `make deps` を先に回すよう言って止まります。組む目標はロック `.lake-build.lock` を取るので、
同じ作業木で 2 つのビルドは重なりません（2 つ目は 1 つ目の終わりを待ちます）。

`make check` は次のスクリプトを回し、最初に失敗したところで止まります。どれも判定を YAML で標準出力に書き、終了コードで結果を
返します（詳しくは各スクリプトの `--help`）。

- `scripts/check-claim-build.sh` — 検証の側の 2 つのパッケージを組みます。組むことに、主張の定理の文が許された層の定義と
  Lean の核だけを使うことの検査（`checkClaimStatements`）、主張の定理が `propext`・`Classical.choice`・`Quot.sound` だけに依る
  ことの検査（`checkClaimAxioms`）、演算の組と正しさ・一致の述語のフィールドの対応の検査（`checkCoverage` など）が含まれます。
  そのあと、2 つの主張の定理と、それが依る定数のすべてを `leanexport` で書き出し、`leanchecker --from-export` で空の環境の
  カーネルに再生します（`status: built`、`kernel_replay: accepted`）。
- `scripts/check-package-dependencies.sh` — パッケージの `require` と、組んだモジュールの `import` が、許された向きだけに
  あることを確かめます。向きの規則は `scripts/package-dependencies.yaml` に書いてあります。
- `scripts/check-testfloat-record.sh` — TestFloat との照合の記録（`riscv-verification/testfloat/records/`）が、いまのソースから
  取ったもので、照合の表の行をすべて持ち、すべて一致したことを確かめます。照合そのものは `make testfloat`
  （`riscv-verification/testfloat/scripts/record_testfloat_level1.sh`。20 分ほどかかります）が走らせ、記録を書き直します。

版の 3 つの検査は `make check` に入っていません。このリポジトリの直下から devshell の中で、1 つずつ回します（ネットワークを
読みます）。`scripts/check-lean-versions.sh`・`scripts/check-mathlib-version.sh`・`scripts/check-nixpkgs-channel.sh` は、
Lean のツールチェイン・Mathlib・nixpkgs の版が、それぞれの最新の安定版にそろっているかを確かめます。

`make check` のスクリプトは、`make build` の後なら 1 つずつ回すこともできます。1 つずつ回したスクリプトはロックを取らないので、
同じ作業木でほかのビルドが走っている間は回さないでください。

## ライセンス

Copyright (c) 2026 Kazutaka Nakamura

Lean のコード（4 つのパッケージ）とスクリプトは、[Apache License 2.0](LICENSE) で提供します。
