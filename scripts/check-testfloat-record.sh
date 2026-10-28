#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed
set -E # let functions and subshells inherit the ERR trap

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/.." && pwd)
pname=$(basename -- "$0")

print_help() {
    cat <<EOF
Name:
    $pname - Judge whether the record of the level 1 comparison with Berkeley
    TestFloat is current, complete and fully matched

Usage:
    $0

Inputs:
    - files
        - riscv-verification/testfloat/records/testfloat-level1.yaml, written
          by riscv-verification/testfloat/scripts/record_testfloat_level1.sh
    - commands
        - scripts/fingerprint-testfloat-sources.sh
        - lake, to build the checker testfloat_check
          (riscv-verification/SoftFloat/RISCV/Test/Main.lean)
        - yq, jq

Outputs:
    A YAML record of the judgement on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  The record was taken from the present sources, has a row for each
           operation and rounding mode of the table of the checker, and every
           vector of every row matched. status: current.
        1  There is no record, or it could not be read, the built Mathlib was
           not fetched (run make deps first; the check does not build Mathlib
           from source), the checker did not build, or a tool is missing. No record of the judgement is written,
           because nothing was judged.
        2  The record was taken from other sources than the present ones: they
           changed since the comparison ran. status: stale.
        4  The record was taken from the present sources and has the rows of
           the table, and some row did not match. status: mismatched.
        8  The record is not a record of level 1 (its level is not 1), or,
           taken from the present sources, its rows are not those of the
           table of the checker: a row is missing, is not in the table, or
           names another declaration than the table does. status: malformed.

Description:
    It does not run the comparison, which takes some twenty minutes; it reads
    the record the comparison left, and compares the fingerprint of the sources
    in the record with that of the present sources
    (scripts/fingerprint-testfloat-sources.sh). The rows the record should
    have are what the checker prints with --list: one line for each rounding
    mode and operation it compares, with the declaration it runs. The checker
    is built for that, and the lines are compared with the rounding mode, the
    operation and the declaration of the rows of the record.

    The level is judged first, as it says what the record is a record of. Staleness is judged before the rows and the mismatches,
    because a stale record was taken with another table and says nothing about
    the present sources.

Notes:
    A stale record says nothing about the present sources: running
    riscv-verification/testfloat/scripts/record_testfloat_level1.sh again
    brings it up to date.
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

record=$based/riscv-verification/testfloat/records/testfloat-level1.yaml
package=$based/riscv-verification

for command_name in lake yq jq; do
    EMSG="line:$LINENO ERROR $command_name is required; run this script in the devShell."
    command -v "$command_name" >/dev/null
done

##############################################################################################
PROGRESS "$LINENO" "checking that the built Mathlib was fetched"

# Without the built Mathlib, lake build builds Mathlib from source, which
# takes hours. make deps fetches it (lake exe cache get).
EMSG="line:$LINENO ERROR the built Mathlib is not in $package/.lake/packages/mathlib; run make deps first."
[ -e "$package/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]

tmpd=$(mktemp -d -t "$pname.$stime.$$.XXXXXXXX")
trap 'rm -rf "$tmpd"' EXIT

##############################################################################################
# ANCHOR: TestFloatRecordCheck
PROGRESS "$LINENO" "reading the record"

EMSG="line:$LINENO ERROR there is no record: $record."
[ -s "$record" ]
yq -o=json -I=0 . "$record" >"$tmpd/record.json"
recorded=$(jq -r '.fingerprint' "$tmpd/record.json")
level=$(jq -r '.level' "$tmpd/record.json")
rows=$(jq -r '.results | length' "$tmpd/record.json")
unmatched=$(jq -r '[.results[] | select(.matched != true)] | length' "$tmpd/record.json")
EMSG="line:$LINENO ERROR the record carries no fingerprint or no row."
[ "$recorded" != null ]
[ "$rows" -gt 0 ]
jq -r '.results[] | "\(.rounding_mode) \(.op) \(.decl)"' "$tmpd/record.json" |
LC_ALL=C sort >"$tmpd/recorded-rows"

PROGRESS "$LINENO" "taking the fingerprint of the present sources"

present=$("$based/scripts/fingerprint-testfloat-sources.sh")

PROGRESS "$LINENO" "listing the table of the checker"

# The output of the build goes to the terminal only when it fails.
EMSG="line:$LINENO ERROR testfloat_check did not build."
lake -d "$package" build testfloat_check >"$tmpd/build" 2>&1 || {
    cat "$tmpd/build" >&3
    false
}
EMSG="line:$LINENO ERROR testfloat_check did not list its table."
"$package/.lake/build/bin/testfloat_check" --list |
LC_ALL=C sort >"$tmpd/expected-rows"
[ -s "$tmpd/expected-rows" ]
expected=$(wc -l <"$tmpd/expected-rows")
missing=$(comm -23 "$tmpd/expected-rows" "$tmpd/recorded-rows" | wc -l)
extra=$(comm -13 "$tmpd/expected-rows" "$tmpd/recorded-rows" | wc -l)

PROGRESS "$LINENO" "judging the record"

if [ "$level" != 1 ]; then
    status=malformed
    code=8
elif [ "$recorded" != "$present" ]; then
    status=stale
    code=2
elif [ "$missing" -gt 0 ] || [ "$extra" -gt 0 ]; then
    status=malformed
    code=8
elif [ "$unmatched" -gt 0 ]; then
    status=mismatched
    code=4
else
    status=current
    code=0
fi
cat <<EOF
check: testfloat-record
generated_at: $stime
result: $([ "$code" = 0 ] && echo true || echo false)
status: $status
record: riscv-verification/testfloat/records/testfloat-level1.yaml
recorded_at: $(jq -r '.recorded_at' "$tmpd/record.json")
level: $level
rows: $rows
expected_rows: $expected
missing_rows: $missing
extra_rows: $extra
unmatched_rows: $unmatched
recorded_fingerprint: $recorded
present_fingerprint: $present
EOF
exit "$code"
# ANCHOR_END: TestFloatRecordCheck

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
