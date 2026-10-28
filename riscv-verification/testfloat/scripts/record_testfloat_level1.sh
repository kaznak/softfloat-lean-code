#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed
set -E # let functions and subshells inherit the ERR trap

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/../../.." && pwd)
# The comparison: its scripts and records are in testfloat/ of the package the
# checker is built in.
package=$based/riscv-verification
testfloat=$package/testfloat
pname=$(basename -- "$0")

print_help() {
    cat <<EOF
Name:
    $pname - Run the level 1 comparison with Berkeley TestFloat in all five
    rounding modes of RISC-V and in rounding to odd, and write its record

Usage:
    [JOBS=<number>] $0

Inputs:
    - environment
        - JOBS: how many rounding modes run at once; by default the number of
          processors (nproc), and at most six, one for each rounding mode
    - commands
        - riscv-verification/testfloat/scripts/run_testfloat_level1.sh, and
          what it needs (testfloat_gen, lake)
        - scripts/fingerprint-testfloat-sources.sh
        - yq, jq

Outputs:
    The record in riscv-verification/testfloat/records/testfloat-level1.yaml,
    replacing the one there,
    and the exit code:

        0  Every vector of every operation in every rounding mode matched.
        1  Nothing was recorded: the built Mathlib was not fetched (run make
           deps first; this script does not build Mathlib from source), a run
           judged nothing for some operation, or a tool is missing.
        2  Some vector did not match. The record is written, with matched:
           false on the rows that did not.

Description:
    The record is what scripts/check-testfloat-record.sh reads. It carries the fingerprint of the sources the runs used
    (scripts/fingerprint-testfloat-sources.sh), the oracle, and one row for each
    operation and rounding mode: the declaration of SoftFloat it ran, the
    number of vectors, the sha256 of what testfloat_gen wrote, and whether
    every result and flag matched.

    The declaration of a row is the one the checker
    (riscv-verification/SoftFloat/RISCV/Test/Main.lean, built as
    testfloat_check) prints for the operation and the rounding mode with
    --list. The checker makes the function it runs and the name it prints from
    one expression of its table, so that the name is that of the declaration
    the function is: a field of a group of instructions or of a set of
    per-format functions, named as the value SoftFloat.RISCV.riscv, the group
    and the field (SoftFloat.RISCV.riscv.instructions.FADD and so on; the
    format is in the name of the operation). A run of an operation that the
    table does not have in its rounding mode stops the recording, and nothing
    is recorded.

Notes:
    Each run deals the vectors of an operation to as many checkers as there
    are processors (run_testfloat_level1.sh), and the runs of the six
    rounding modes go at once, so that the short operations of one overlap the
    long ones of another. A checker holds little memory (it reads the vectors
    as a stream, some 12 MiB at most), and the vectors are never written to a
    file. The logs of the runs stay in
    riscv-verification/testfloat/logs/, out of git; the record keeps only the
    summary.
EOF
}

##############################################################################################
exec 3>&2
# The unreachable marker at the end of this script makes the ERR trap look
# unreachable as well, and these are then reported as never invoked.
# shellcheck disable=SC2329
MSG() {
    echo "$pname pid:$$ stime:$stime etime:$(date -u +%Y%m%dT%H%M%SZ) $*" >&3
}

trap 'ERROR_HANDLER' ERR
EMSG="line:$LINENO ERROR"
# shellcheck disable=SC2329
ERROR_HANDLER() {
    MSG "line:$LINENO ERROR status ${PIPESTATUS[*]}"
    [ "$EMSG" ] && MSG "$EMSG"
    MSG "line:$LINENO EXIT with error."
    exit 1
}

PROGRESS() {
    local lineno="$1"
    shift
    local PMSG="$*"
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

##############################################################################################
PROGRESS "$LINENO" "checking that the built Mathlib was fetched"

# Without the built Mathlib, lake build builds Mathlib from source, which
# takes hours. make deps fetches it (lake exe cache get).
EMSG="line:$LINENO ERROR the built Mathlib is not in $package/.lake/packages/mathlib; run make deps first."
[ -e "$package/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]

tmpd=$(mktemp -d -t "$pname.$stime.$$.XXXXXXXX")
trap 'rm -rf "$tmpd"' EXIT

##############################################################################################
PROGRESS "$LINENO" "taking the fingerprint of the sources"

fingerprint=$("$based/scripts/fingerprint-testfloat-sources.sh")

##############################################################################################
PROGRESS "$LINENO" "running the comparison in each rounding mode"

printf '%s\n' near_even minMag min max near_maxMag odd >"$tmpd/rms"
jobs=${JOBS:-$(nproc)}
EMSG="line:$LINENO ERROR JOBS is not a positive number: $jobs."
[[ $jobs =~ ^[1-9][0-9]*$ ]]
# Built once here, so that the runs started together find it built.
EMSG="line:$LINENO ERROR testfloat_check did not build."
lake -d "$package" build testfloat_check >&2
# The table of the checker: the rounding mode, the operation and the
# declaration it runs, on each line.
EMSG="line:$LINENO ERROR testfloat_check did not list its table."
"$package/.lake/build/bin/testfloat_check" --list |
jq -R -c 'split(" ") | {rounding_mode: .[0], op: .[1], decl: .[2]}' >"$tmpd/table"
# Each run writes its report and its exit code in files of its own.
# The body is given in single quotes so that bash -c, not this shell, expands it.
# shellcheck disable=SC2016
xargs -P "$jobs" -I%%rm%% bash -c '
    status=0
    OPS=ALL RM=$2 "$1/scripts/run_testfloat_level1.sh" >"$3/run.$2.yaml" || status=$?
    echo "$2 $status" >"$3/status.$2"
    ' _ "$testfloat" %%rm%% "$tmpd" <"$tmpd/rms"
cat "$tmpd/rms" | xargs -I%%rm%% cat "$tmpd/status.%%rm%%" >"$tmpd/statuses"

PROGRESS "$LINENO" "checking that every run judged every operation"

# Exit code 1 of a run is that it judged nothing for some operation.
grep ' 1$' "$tmpd/statuses" >"$tmpd/judged-nothing" || true
EMSG="line:$LINENO ERROR a run judged nothing: $(tr '\n' ' ' <"$tmpd/judged-nothing")"
[ ! -s "$tmpd/judged-nothing" ]

##############################################################################################
PROGRESS "$LINENO" "writing the record"

cat "$tmpd/rms" |
xargs -I%%rm%% yq -o=json -I=0 . "$tmpd/run.%%rm%%.yaml" >"$tmpd/runs"
jq -s --arg fingerprint "$fingerprint" --arg stime "$stime" --slurpfile table "$tmpd/table" '
    # The declaration each operation runs in each rounding mode, as the
    # checker names it.
    ($table | map({key: "\(.rounding_mode) \(.op)", value: .decl}) | from_entries) as $decls
    | def decl($rm): $decls["\($rm) \(.)"] // error("the checker has no \(.) in \($rm)");
    {level: 1,
     recorded_at: $stime,
     fingerprint: $fingerprint,
     oracle: .[0].host.testfloat_gen,
     seed: .[0].seed,
     arch: .[0].host.arch,
     results: [ .[] | .rounding_mode as $rm | .ops[]
                | {rounding_mode: $rm, op, decl: (.op | decl($rm)), vectors, oracle_sha256, matched} ]}
    ' "$tmpd/runs" |
yq -P -o=yaml . >"$tmpd/record.yaml"
mv -f "$tmpd/record.yaml" "$testfloat/records/testfloat-level1.yaml"

MSG "line:$LINENO INFO recorded $(yq '.results | length' "$testfloat/records/testfloat-level1.yaml") rows in riscv-verification/testfloat/records/testfloat-level1.yaml"
if grep -q ' 2$' "$tmpd/statuses"; then
    exit 2
fi
exit 0

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
