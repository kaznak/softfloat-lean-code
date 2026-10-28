#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed
set -E # let functions and subshells inherit the ERR trap

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/.." && pwd)
# The package the checker is built in: riscv-verification/, above testfloat/.
package=$(cd -- "$based/.." && pwd)
pname=$(basename -- "$0")

print_help() {
    cat <<EOF
Name:
    $pname - Check SoftFloatLean against the level 1 test vectors of Berkeley TestFloat

Usage:
    [RM=<rounding mode>] [OPS=<ALL|F16|"<op> ...">] [SHARDS=<number>] $0
    $0 --list
        - Print the operations that OPS=ALL checks, one per line, and exit.

Inputs:
    - commands
        - testfloat_gen, built with the RISC-V specialization (the devShell provides it)
        - lake
    - environment variables
        - RM
            The rounding mode, by its TestFloat name. The names are listed in
            all-rms in this script, beside the IEEE 754 names. Default near_even.
            odd is rounding to odd, which is not an attribute of IEEE 754 nor a
            rounding mode of RISC-V; the checker runs the per-format functions
            with the rounding direction roundToOdd of Core for it, and
            vfncvt.rod.f.f.w for f64_to_f32 and f32_to_f16.
        - OPS
            Which operations to check. The list they are taken from is all-ops
            in this script: the 102 operations that both testfloat_gen and
            testfloat_check know.
                ALL (default)  all 102; with RM=odd, all but bf16_to_f32
                               (101), since there is no per-format value of
                               BF16 to run it with, and it does not round.
                F16            the 28 on binary16, whose names contain f16
                               (not bf16).
                <op> ...       the named ones, separated by spaces.
        - SHARDS
            Into how many checkers the vectors of one operation are dealt. By
            default the number of processors (nproc).

Outputs:
    A YAML record on standard output. For each operation it gives the number of
    vectors, the sha256 of what testfloat_gen wrote, and whether every result and
    flag matched. A log of the run is written to logs/<stime>.<pid>.log.
    The exit code is one of:
        0  Every vector of every operation matched.
        1  Nothing was judged for some operation: a tool is missing, the built
           Mathlib was not fetched (run make deps first; this script does not
           build Mathlib from source), the checker did not build, or the
           checker did not know the operation.
        2  Some vector did not match.

Description:
    For each operation, testfloat_gen writes the inputs with the expected results and
    flags, and testfloat_check (SoftFloat/RISCV/Test/Main.lean) runs SoftFloatLean on the same
    inputs and compares.

    The vectors go as a stream, never to a file: split deals their lines in turn
    to SHARDS checkers running at once, and the number of lines and the sha256
    are taken from the whole stream on the way. A line is a test case of its
    own, so the shards are judged apart and summed: the operation matched when
    every shard read its lines without a mismatch or a line it could not read,
    and the shards together read every line. The cost of an operation varies
    by orders of magnitude (fused multiply-add is most of it), and dealing its
    vectors keeps every processor busy on the long ones.

Notes:
    The sha256 identifies the oracle output. Runs on different hosts are meant to
    agree on it; compare the records to see that they do.
    Every operation is generated with testfloat_gen -exact, so rounding to an integer
    raises the inexact flag as FROUNDNX and the conversions to integers of RISC-V do.
    Operations that do not round to an integer ignore the option. The exception is
    an operation whose name ends in _notexact (f32_roundToInt_notexact and the
    like): it is the operation of TestFloat named without the suffix, generated
    with -notexact, so that rounding to an integer does not raise inexact, as
    FROUND does.
EOF
}

##############################################################################################
mkdir -p "$based/logs"
log=$based/logs/$stime.$$.log
exec 3>&2 2>"$log"
# The unreachable marker at the end of this script makes the ERR trap look
# unreachable as well, and these are then reported as never invoked.
# shellcheck disable=SC2329
# Also written to the log, so the log reads in order with the commands' output.
MSG() {
    local line
    line="$pname pid:$$ stime:$stime etime:$(date -u +%Y%m%dT%H%M%SZ) $*"
    echo "$line" >&3
    echo "$line" >&2
}

trap 'ERROR_HANDLER' ERR
EMSG="line:$LINENO ERROR"
# shellcheck disable=SC2329
ERROR_HANDLER()	{
    MSG "line:$LINENO ERROR status ${PIPESTATUS[*]}"
    [ "$EMSG" ] && MSG "$EMSG"
    MSG "line:$LINENO EXIT with error."
    exit 1
}

PROGRESS() {
    local lineno="$1"
    shift
    local PMSG="$*"
    # MSG "line:$lineno INFO $PMSG"
    EMSG="line:$lineno ERROR while ${PMSG}."
}

##############################################################################################
PROGRESS "$LINENO" "checking arguments"

case "${1:-}" in
-h | --help)
    print_help
    exit 0
    ;;
esac

tmpd=$(mktemp -d -t "$pname.$stime.$$.XXXXXXXX")
trap 'rm -rf "$tmpd"' EXIT

# The rounding modes of IEEE 754, by their TestFloat names. TestFloat's -rodd is
# left out: round to odd is not one of them.
sed 's/#.*//' <<EOF | tr -s ' \n' '\n' | sed '/^$/d' >"$tmpd/all-rms"
# TestFloat     IEEE 754             rounds
near_even     # roundTiesToEven      to nearest, ties to even
near_maxMag   # roundTiesToAway      to nearest, ties away from zero
minMag        # roundTowardZero      toward zero
min           # roundTowardNegative  toward negative infinity
max           # roundTowardPositive  toward positive infinity
odd           # roundToOdd           to odd (not an attribute of IEEE 754)
EOF

sort "$tmpd/all-rms" | uniq -d >"$tmpd/duplicate-rms"
EMSG="line:$LINENO ERROR rounding mode listed more than once in all-rms: $(tr '\n' ' ' <"$tmpd/duplicate-rms")"
[ ! -s "$tmpd/duplicate-rms" ]

RM=${RM:-near_even}
EMSG="line:$LINENO ERROR unknown rounding mode in RM: $RM"
grep -Fqx "$RM" "$tmpd/all-rms"

# Every operation that both testfloat_gen and testfloat_check know.
sed 's/#.*//' <<EOF | tr -s ' \n' '\n' | sed '/^$/d' >"$tmpd/all-ops"
# binary16
## arithmetic, fused multiply-add, rounding to an integral value
f16_add f16_sub f16_mul f16_div f16_sqrt f16_mulAdd f16_roundToInt
## rounding to an integral value with -notexact (not raising inexact)
f16_roundToInt_notexact
## comparisons: eq raises invalid only for signaling NaNs, lt and le for any NaN;
## the _signaling and _quiet variants swap that behavior
f16_eq f16_eq_signaling f16_lt f16_lt_quiet f16_le f16_le_quiet
## conversions to and from the other formats
f16_to_f32 f16_to_f64 f32_to_f16 f64_to_f16
## conversions to integers
f16_to_i32 f16_to_ui32 f16_to_i64 f16_to_ui64
## conversions from integers
i32_to_f16 ui32_to_f16 i64_to_f16 ui64_to_f16

# binary32
## arithmetic, fused multiply-add, rounding to an integral value
f32_add f32_sub f32_mul f32_div f32_sqrt f32_mulAdd f32_roundToInt
f32_roundToInt_notexact
## comparisons
f32_eq f32_eq_signaling f32_lt f32_lt_quiet f32_le f32_le_quiet
## conversions to and from binary64 (those with binary16 are under binary16)
f32_to_f64 f64_to_f32
## conversions to integers
f32_to_i32 f32_to_ui32 f32_to_i64 f32_to_ui64
## conversions from integers
i32_to_f32 ui32_to_f32 i64_to_f32 ui64_to_f32

# binary64 (riscv.conversions to binary16 and binary32 are listed under them)
## arithmetic, fused multiply-add, rounding to an integral value
f64_add f64_sub f64_mul f64_div f64_sqrt f64_mulAdd f64_roundToInt
f64_roundToInt_notexact
## comparisons
f64_eq f64_eq_signaling f64_lt f64_lt_quiet f64_le f64_le_quiet
## conversions to integers
f64_to_i32 f64_to_ui32 f64_to_i64 f64_to_ui64
## conversions from integers
i32_to_f64 ui32_to_f64 i64_to_f64 ui64_to_f64

# binary128
## arithmetic, fused multiply-add, rounding to an integral value
f128_add f128_sub f128_mul f128_div f128_sqrt f128_mulAdd f128_roundToInt
f128_roundToInt_notexact
## comparisons
f128_eq f128_eq_signaling f128_lt f128_lt_quiet f128_le f128_le_quiet
## conversions to and from the other formats
f16_to_f128 f32_to_f128 f64_to_f128 f128_to_f16 f128_to_f32 f128_to_f64
## conversions to integers
f128_to_i32 f128_to_ui32 f128_to_i64 f128_to_ui64
## conversions from integers
i32_to_f128 ui32_to_f128 i64_to_f128 ui64_to_f128

# BF16 (Zfbfmin): the conversions with binary32. testfloat_gen does not list
# bf16 in -help, but generates both, and f32_to_bf16 in the rounding mode of -r.
f32_to_bf16 bf16_to_f32
EOF

sort "$tmpd/all-ops" | uniq -d >"$tmpd/duplicate-ops"
EMSG="line:$LINENO ERROR operation listed more than once in all-ops: $(tr '\n' ' ' <"$tmpd/duplicate-ops")"
[ ! -s "$tmpd/duplicate-ops" ]

case "${1:-}" in
-l | --list)
    cat "$tmpd/all-ops"
    exit 0
    ;;
esac

case "${OPS:-ALL}" in
ALL)
    if [ "$RM" = odd ]; then
        grep -Fxv bf16_to_f32 "$tmpd/all-ops"
    else
        cat "$tmpd/all-ops"
    fi
    ;;
F16)
    grep -E '(^|_)f16(_|$)' "$tmpd/all-ops"
    ;;
*)
    echo "$OPS" | tr -s ' ' '\n' | sed '/^$/d'
    ;;
esac >"$tmpd/ops"

EMSG="line:$LINENO ERROR no operation to check."
[ -s "$tmpd/ops" ]

# grep exits 1 when every name is known, which is the case to go on with.
grep -Fxv -f "$tmpd/all-ops" "$tmpd/ops" >"$tmpd/unknown-ops" || true
EMSG="line:$LINENO ERROR unknown operation in OPS: $(tr '\n' ' ' <"$tmpd/unknown-ops")"
[ ! -s "$tmpd/unknown-ops" ]

##############################################################################################
PROGRESS "$LINENO" "checking required commands"

for command_name in testfloat_gen lake sha256sum jq yq; do
    EMSG="line:$LINENO ERROR $command_name is required; run this script in the devShell."
    command -v "$command_name" >/dev/null
done

##############################################################################################
PROGRESS "$LINENO" "checking that the built Mathlib was fetched"

# Without the built Mathlib, lake build builds Mathlib from source, which
# takes hours. make deps fetches it (lake exe cache get).
EMSG="line:$LINENO ERROR the built Mathlib is not in $package/.lake/packages/mathlib; run make deps first."
[ -e "$package/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]

##############################################################################################
PROGRESS "$LINENO" "building testfloat_check"

EMSG="line:$LINENO ERROR testfloat_check did not build."
lake -d "$package" build testfloat_check >&2

: >"$tmpd/results"

shards=${SHARDS:-$(nproc)}
EMSG="line:$LINENO ERROR SHARDS is not a positive number: $shards."
[[ $shards =~ ^[1-9][0-9]*$ ]]
mkfifo "$tmpd/to-count" "$tmpd/to-hash"
# The seed of the pseudo-random cases testfloat_gen draws, given rather than left to
# its default, so that the record says which cases were drawn.
seed=1

##############################################################################################
# The loop runs in a subshell, so what PROGRESS sets inside it does not come back here.
PROGRESS "$LINENO" "checking the operations"

cat "$tmpd/ops" |
while read -r op; do
    PROGRESS "$LINENO" "checking $op"

    mkdir "$tmpd/shards.$op"
    # The name of the operation in TestFloat, and whether rounding to an integer
    # raises inexact.
    case $op in
    *_notexact)
        genop=${op%_notexact}
        exactness=-notexact
        ;;
    *)
        genop=$op
        exactness=-exact
        ;;
    esac
    wc -l <"$tmpd/to-count" >"$tmpd/vectors.$op" &
    counter=$!
    sha256sum <"$tmpd/to-hash" | cut -d' ' -f1 >"$tmpd/sha256.$op" &
    hasher=$!
    # split runs the filter for each shard with FILE set to the name the shard
    # would have; the checker writes its report and its exit code beside it.
    # -exact and -notexact are ignored by operations that do not round to an integer.
    # The filter is given in single quotes so that the shell of split, not this
    # one, expands FILE and $?.
    # shellcheck disable=SC2016
    testfloat_gen -level 1 -seed "$seed" "$exactness" "$genop" "-r$RM" |
    tee "$tmpd/to-count" "$tmpd/to-hash" |
    split -n "r/$shards" -a 4 --filter="$(printf '%q %q %q /dev/stdin >"$FILE.out" 2>"$FILE.err"; echo $? >"$FILE.status"' \
        "$package/.lake/build/bin/testfloat_check" "$op" "$RM")" - "$tmpd/shards.$op/"
    wait "$counter"
    wait "$hasher"
    vectors=$(cat "$tmpd/vectors.$op")
    sha256=$(cat "$tmpd/sha256.$op")
    cat "$tmpd/shards.$op"/*.out >&2

    # testfloat_check exits 1 on a mismatch (or on no line at all) and 2 when it
    # cannot judge; it writes to stderr only when it cannot judge. The reason
    # goes to the terminal as well, since stderr otherwise reaches only the log.
    cat "$tmpd/shards.$op"/*.status | grep -vx '[01]' >"$tmpd/unjudged.$op" || true
    if [ -s "$tmpd/unjudged.$op" ]; then
        cat "$tmpd/shards.$op"/*.err | tee /dev/fd/3 >&2
    fi
    EMSG="line:$LINENO ERROR testfloat_check could not judge $op."
    [ ! -s "$tmpd/unjudged.$op" ]
    # The last line but one of each report sums up its shard; a shard that got
    # no line reports total=0 and exits 1, which is not a mismatch.
    grep -h "^$op -r$RM: total=" "$tmpd/shards.$op"/*.out |
    sed 's/.*total=\([0-9]*\) result_mismatch=\([0-9]*\) flag_mismatch=\([0-9]*\) parse_error=\([0-9]*\)$/\1 \2 \3 \4/' |
    awk '{t += $1; m += $2 + $3 + $4} END {print t + 0, m + 0}' >"$tmpd/sum.$op"
    EMSG="line:$LINENO ERROR some shard of $op did not report."
    [ "$(grep -hc "^$op -r$RM: total=" "$tmpd/shards.$op"/*.out | awk '{n += $1} END {print n}')" -eq "$shards" ]
    if [ "$(cat "$tmpd/sum.$op")" = "$vectors 0" ] && [ "$vectors" -gt 0 ]; then
        matched=true
        MSG "line:$LINENO INFO $op -r$RM: matched ($vectors vectors in $shards shards, sha256 $sha256)"
    else
        matched=false
        MSG "line:$LINENO INFO $op -r$RM: MISMATCHED ($vectors vectors in $shards shards, read and mismatched: $(cat "$tmpd/sum.$op"), sha256 $sha256)"
    fi
    rm -r "$tmpd/shards.$op"

    jq -n -c \
        --arg op "$op" \
        --argjson vectors "$vectors" \
        --arg sha256 "$sha256" \
        --argjson matched "$matched" \
        '{op: $op, vectors: $vectors, oracle_sha256: $sha256, matched: $matched}' |
        tee -a "$tmpd/results" >&2
done

##############################################################################################
PROGRESS "$LINENO" "printing the report"

jq -s \
    --arg stime "$stime" \
    --arg rm "$RM" \
    --arg arch "$(uname -m)" \
    --arg generator "$(command -v testfloat_gen)" \
    --argjson seed "$seed" \
    --arg log "${log#"$based"/}" '
    {
        check: "testfloat",
        generated_at: $stime,
        result: all(.[]; .matched),
        level: 1,
        rounding_mode: $rm,
        host: {arch: $arch, testfloat_gen: $generator},
        seed: $seed,
        log: $log,
        ops: .
    }
    ' "$tmpd/results" >"$tmpd/report.json"

yq -p json -o yaml '.' "$tmpd/report.json"

##############################################################################################
PROGRESS "$LINENO" "exiting"

if jq -e '.result' "$tmpd/report.json" >/dev/null; then
    exit 0
fi
exit 2

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
