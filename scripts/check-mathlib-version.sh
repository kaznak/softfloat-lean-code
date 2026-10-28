#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed
set -E # let functions and subshells inherit the ERR trap

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/.." && pwd)
pname=$(basename -- "$0")

# Relative to where the caller stands, so the help prints what they can type.
devshell=$(realpath -m --relative-to=. -- "$based/scripts/restricted-devshell.sh")

print_help() {
    cat <<EOF
Name:
    $pname - Compare the Lean toolchain and the Mathlib revision pinned by
    this repository against the latest stable Mathlib release

Usage:
    $devshell $0

Inputs:
    - files
        - lean-toolchain
        - core-verification/lakefile.toml and riscv-verification/lakefile.toml,
          for the rev of mathlib
        - core-verification/lake-manifest.json and
          riscv-verification/lake-manifest.json, for the commit of mathlib
          they resolve
    - network
        - https://api.github.com
        - https://raw.githubusercontent.com

Outputs:
    A YAML record of the comparison on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  The pinned toolchain is the one the latest stable Mathlib release
           pins, core-verification/ and riscv-verification/ require Mathlib at
           the tag of that release, and their manifests resolve it to the same
           commit. The record reads status: aligned.
        1  A required tool is missing, or the release, a lakefile.toml or a
           lake-manifest.json could not be read. No record is written,
           because nothing was judged.
        2  An update is available: the pinned toolchain differs from the one
           the latest stable Mathlib release pins, or core-verification/ or
           riscv-verification/ requires Mathlib at an older stable tag. The
           record reads status: update-available.
        3  The upstream did not answer (it is unreachable, or an unauthenticated
           rate limit or a transient error). No record is written, because
           nothing was judged.
        4  core-verification/ or riscv-verification/ does not require Mathlib,
           or requires it at a rev that is not the tag of a stable release (a
           commit, a branch, a release candidate), or the two manifests
           resolve Mathlib to different commits. The record reads
           status: deviated.

Description:
    The latest stable release of Mathlib is the release GitHub marks as latest,
    which is never a release candidate. Its lean-toolchain is the toolchain this
    repository follows; the script compares it with lean-toolchain here. The
    tag of that release is the rev of Mathlib that
    core-verification/lakefile.toml and riscv-verification/lakefile.toml are
    to require; the script compares it with theirs. The two packages of the
    verification each require Mathlib and each keep, in lake-manifest.json,
    the commit Lake resolved it to; the commits are to be the same, so that
    the two are built against one Mathlib.
    Whether CSLib agrees is checked apart, by scripts/check-lean-versions.sh.

Notes:
    This script reads the network. Any failure to get a response from
    api.github.com or raw.githubusercontent.com, including total unreachability,
    is reported as exit 3, not 1. The update is reported, not made: neither
    lean-toolchain nor a lakefile.toml is ever rewritten. A stable tag is told
    by its form, vMAJOR.MINOR.PATCH; a rev of that form other than the latest
    is taken as an older stable release without asking the upstream.
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

# The upstream did not answer. Exit 3, not the ERROR_HANDLER's 1, so a caller
# can tell this apart from a missing tool.
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

# ANCHOR: MathlibVersion
##############################################################################################
PROGRESS "$LINENO" "resolving the latest stable Mathlib release"

if ! mathlib_release=$(
    curl --fail --silent --show-error \
        "https://api.github.com/repos/leanprover-community/mathlib4/releases/latest" |
        yq --exit-status --unwrapScalar '.tag_name'
); then
    network_failure "resolving the latest stable Mathlib release"
fi

##############################################################################################
PROGRESS "$LINENO" "resolving the Lean toolchain that Mathlib pins"

if ! mathlib_toolchain=$(
    curl --fail --silent --show-error \
        "https://raw.githubusercontent.com/leanprover-community/mathlib4/$mathlib_release/lean-toolchain"
); then
    network_failure "resolving the Lean toolchain Mathlib $mathlib_release pins"
fi

##############################################################################################
PROGRESS "$LINENO" "reading lean-toolchain in this repository"

EMSG="line:$LINENO ERROR cannot read lean-toolchain in this repository."
selected_toolchain=$(sed -n '1p' "$based/lean-toolchain")

##############################################################################################
PROGRESS "$LINENO" "reading the Mathlib revisions that the packages of the verification require"

# Empty when the package does not require Mathlib.
EMSG="line:$LINENO ERROR cannot read core-verification/lakefile.toml."
core_rev=$(yq -p toml -o yaml '.require[] | select(.name == "mathlib") | .rev // ""' "$based/core-verification/lakefile.toml")
EMSG="line:$LINENO ERROR cannot read riscv-verification/lakefile.toml."
riscv_rev=$(yq -p toml -o yaml '.require[] | select(.name == "mathlib") | .rev // ""' "$based/riscv-verification/lakefile.toml")

##############################################################################################
PROGRESS "$LINENO" "reading the Mathlib commits the manifests of the verification resolve"

# Empty when the manifest has no Mathlib.
EMSG="line:$LINENO ERROR cannot read core-verification/lake-manifest.json."
core_commit=$(yq -p json -o yaml '.packages[] | select(.name == "mathlib") | .rev // ""' "$based/core-verification/lake-manifest.json")
EMSG="line:$LINENO ERROR cannot read riscv-verification/lake-manifest.json."
riscv_commit=$(yq -p json -o yaml '.packages[] | select(.name == "mathlib") | .rev // ""' "$based/riscv-verification/lake-manifest.json")

##############################################################################################
PROGRESS "$LINENO" "judging the pinned toolchain and revisions"

status=aligned
[ "$selected_toolchain" = "$mathlib_toolchain" ] || status=update-available
for rev in "$core_rev" "$riscv_rev"; do
    if [ "$rev" = "$mathlib_release" ]; then
        continue
    elif [[ $rev =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
        [ "$status" = deviated ] || status=update-available
    else
        status=deviated
    fi
done
# The two packages built against different commits of Mathlib.
if [ -z "$core_commit" ] || [ "$core_commit" != "$riscv_commit" ]; then
    status=deviated
fi
if [ "$status" = aligned ]; then
    result=true
else
    result=false
fi

##############################################################################################
PROGRESS "$LINENO" "printing the report"

yq '.' <<EOF
check: mathlib-version
generated_at: "$stime"
result: $result
status: $status
expected_lean_toolchain: "$mathlib_toolchain"
expected_mathlib_rev: "$mathlib_release"
observed:
  mathlib:
    release: "$mathlib_release"
    lean_toolchain: "$mathlib_toolchain"
  this_repository:
    lean_toolchain: "$selected_toolchain"
    mathlib_rev:
      core-verification: "$core_rev"
      riscv-verification: "$riscv_rev"
    mathlib_commit:
      core-verification: "$core_commit"
      riscv-verification: "$riscv_commit"
EOF

##############################################################################################
PROGRESS "$LINENO" "exiting"

case "$status" in
aligned)
    exit 0
    ;;
update-available)
    exit 2
    ;;
*)
    exit 4
    ;;
esac
# ANCHOR_END: MathlibVersion

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
