#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/.." && pwd)
pname=$(basename -- "$0")

# Relative to where the caller stands, so the help prints what they can type.
devshell=$(realpath -m --relative-to=. -- "$based/scripts/restricted-devshell.sh")

print_help() {
    cat <<EOF
Name:
    $pname - Compare the Lean toolchain pinned by this repository against the latest
    stable CSLib, Mathlib and Lean releases

Usage:
    $devshell $0

Inputs:
    - files
        - lean-toolchain
    - network
        - https://api.github.com
        - https://raw.githubusercontent.com

Outputs:
    A YAML record of the comparison on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  The pinned toolchain already matches the latest stable release.
           The record reads status: aligned.
        1  The check could not be carried out (a required tool is missing, or
           the script failed). No record is written, because nothing was judged.
        2  An update is available: the pinned toolchain differs from the latest.
           The record reads status: update-available.
        3  The upstream did not answer (it is unreachable, or an unauthenticated
           rate limit or a transient error). No record is written, because nothing
           was judged.
        4  The latest CSLib, Mathlib and Lean releases do not agree with each other.
           No record is written, because there is no single version to compare
           with.

Description:
    CSLib pins a Mathlib revision, and that Mathlib revision pins a Lean toolchain.
    This script follows that chain from the latest CSLib release down to the Lean
    toolchain it implies, and compares the result with the toolchain this repository
    pins in lean-toolchain.

Notes:
    The three upstream projects release on their own schedules, so there are moments
    when they disagree. Exit code 4 reports that state instead of proposing an update,
    because while they disagree there is no single version to move to. It is not
    the 1 of a failure, so that a caller can tell a disagreement upstream from a
    check that broke.

    This script reads the network. Any failure to get a response from
    api.github.com or raw.githubusercontent.com, including total unreachability,
    is reported as exit 3, not 1, so that a caller can distinguish "could not
    judge because the network failed" from "could not judge because a tool is
    missing or the script failed".
EOF
}

##############################################################################################
exec 3>&2
# The unreachable marker at the end of this script makes the ERR trap look
# unreachable as well, and these are then reported as never invoked.
# shellcheck disable=SC2329
MSG() {
    echo "$pname pid:$$ stime:$stime etime:$(date -u +%Y%m%dT%H%M%SZ) $*"	>&3
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

# The upstream did not answer (it is unreachable, or an unauthenticated rate
# limit or a transient error). Exit 3, not the ERROR_HANDLER's 1, so a caller can tell
# this apart from a missing tool or a failure of the script.
network_failure() {
    MSG "line:$LINENO WARN upstream API did not respond while $*"
    exit 3
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
PROGRESS "$LINENO" "checking required commands"

for command_name in curl yq; do
    EMSG="line:$LINENO ERROR $command_name is required; run this script through $devshell."
    command -v "$command_name" >/dev/null
done

# ANCHOR: LeanVersions
##############################################################################################
PROGRESS "$LINENO" "resolving the latest CSLib release"

github_raw=https://raw.githubusercontent.com

if ! cslib_release=$(
    curl --fail --silent --show-error \
        "https://api.github.com/repos/leanprover/cslib/releases/latest" |
        yq --exit-status --unwrapScalar '.tag_name'
); then
    network_failure "resolving the latest CSLib release"
fi

if ! cslib_toolchain=$(
    curl --fail --silent --show-error \
        "$github_raw/leanprover/cslib/$cslib_release/lean-toolchain"
); then
    network_failure "resolving the Lean toolchain CSLib $cslib_release pins"
fi

##############################################################################################
PROGRESS "$LINENO" "resolving the Mathlib revision that CSLib pins"

if ! mathlib_release=$(
    curl --fail --silent --show-error \
        "$github_raw/leanprover/cslib/$cslib_release/lakefile.toml" |
        yq --input-format toml --exit-status --unwrapScalar \
            '.require[] | select(.name == "mathlib") | .rev'
); then
    network_failure "resolving the Mathlib revision CSLib $cslib_release pins"
fi

##############################################################################################
PROGRESS "$LINENO" "resolving the Lean toolchain that Mathlib pins"

if ! mathlib_toolchain=$(
    curl --fail --silent --show-error \
        "$github_raw/leanprover-community/mathlib4/$mathlib_release/lean-toolchain"
); then
    network_failure "resolving the Lean toolchain Mathlib $mathlib_release pins"
fi

##############################################################################################
PROGRESS "$LINENO" "reading lean-toolchain in this repository"

EMSG="line:$LINENO ERROR cannot read lean-toolchain in this repository."
selected_toolchain=$(sed -n '1p' "$based/lean-toolchain")
expected_toolchain="leanprover/lean4:$cslib_release"

##############################################################################################
PROGRESS "$LINENO" "judging the pinned toolchain"

# The upstream releases disagree: a result, not a failure, so not the 1 of the
# ERROR_HANDLER.
if [ "$mathlib_release" != "$cslib_release" ] ||
    [ "$cslib_toolchain" != "$expected_toolchain" ] ||
    [ "$mathlib_toolchain" != "$expected_toolchain" ]; then
    MSG "line:$LINENO WARN latest stable CSLib ($cslib_release, $cslib_toolchain), Mathlib ($mathlib_release, $mathlib_toolchain) and Lean versions are not aligned."
    exit 4
fi

if [ "$selected_toolchain" = "$expected_toolchain" ]; then
    status=aligned
else
    status=update-available
fi

# Reported by every check, so a caller reads .result without knowing this one's
# vocabulary.
if [ "$status" = aligned ]; then
    result=true
else
    result=false
fi

##############################################################################################
PROGRESS "$LINENO" "printing the report"

yq '.' <<EOF
check: lean-versions
generated_at: "$stime"
result: $result
status: $status
expected_lean_toolchain: "$expected_toolchain"
observed:
  cslib:
    release: "$cslib_release"
    lean_toolchain: "$cslib_toolchain"
  mathlib:
    release: "$mathlib_release"
    lean_toolchain: "$mathlib_toolchain"
  this_repository:
    lean_toolchain: "$selected_toolchain"
EOF

################################################################
PROGRESS "$LINENO" "exiting"

case "$status" in
aligned)
    exit 0
    ;;
*)
    exit 2
    ;;
esac
# ANCHOR_END: LeanVersions

# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
