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
    $pname - Print the fingerprint of the sources that the comparison with
    Berkeley TestFloat runs

Usage:
    $0

Inputs:
    - files
        - core-operators/, riscv-operators/ and
          riscv-verification/SoftFloat/RISCV/Test/: the .lean files (except
          .lake/)
        - core-operators/ and riscv-operators/: lakefile.toml and
          lean-toolchain
        - riscv-verification/testfloat/scripts/run_testfloat_level1.sh and
          record_testfloat_level1.sh beside it
        - nix/softfloat-riscv.nix and nix/testfloat-riscv.nix, the nix
          definitions of the oracle (SoftFloat and TestFloat built for RISC-V)

Outputs:
    The fingerprint on standard output, one line of 64 hexadecimal digits, and
    the exit code 0. Exit code 1 if a file could not be read.

Description:
    The fingerprint is the sha256 of the list of the files above, one line each
    with the sha256 of its content and its path relative to the repository, in
    sorted order. A record of the comparison carries the fingerprint of what it
    ran, so that a record taken before the sources changed is seen to be stale.

    The lakefile.toml of riscv-verification/, the package the comparison is
    built in, is left out: it requires Mathlib and core-verification/ as well,
    which take no part in the comparison, so that a change of the version of
    Mathlib does not make the record stale.

Notes:
    The files are read as they are in the working tree, committed or not.
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
# ANCHOR: TestFloatFingerprint
PROGRESS "$LINENO" "listing and hashing the sources"

{
    find "$based/core-operators" "$based/riscv-operators" "$based/riscv-verification/SoftFloat/RISCV/Test" \
        -name .lake -prune -o -type f -name '*.lean' -print
    printf '%s\n' "$based"/core-operators/lakefile.toml "$based"/core-operators/lean-toolchain \
        "$based"/riscv-operators/lakefile.toml "$based"/riscv-operators/lean-toolchain \
        "$based"/riscv-verification/testfloat/scripts/run_testfloat_level1.sh \
        "$based"/riscv-verification/testfloat/scripts/record_testfloat_level1.sh \
        "$based"/nix/softfloat-riscv.nix "$based"/nix/testfloat-riscv.nix
} |
sed "s|^$based/||" |
LC_ALL=C sort |
(cd "$based" && xargs -d '\n' sha256sum) |
sha256sum |
cut -d' ' -f1
# ANCHOR_END: TestFloatFingerprint
exit 0

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
