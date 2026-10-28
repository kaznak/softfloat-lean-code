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
    $pname - Compare the nixpkgs channel referenced by flake.lock against the latest
    stable release channel

Usage:
    $devshell $0

Inputs:
    - files
        - flake.lock
    - network
        - https://raw.githubusercontent.com

Outputs:
    A YAML record of the comparison on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  flake.lock already references the latest stable release channel.
           The record reads status: aligned.
        1  The check could not be carried out (a required tool is missing, or
           the script failed). No record is written, because nothing was judged.
        2  A newer stable release channel exists.
           The record reads status: update-available.
        3  The upstream did not answer (it is unreachable, or an unauthenticated
           rate limit or a transient error). No record is written, because nothing
           was judged.
        4  flake.lock references a channel outside the policy below. The record reads
           status: unstable-channel or status: unexpected-ref. It is not the 1 of a
           failure, so that a caller can tell a channel against the policy from a
           check that broke.

Description:
    This repository follows the latest stable nixos-YY.MM release channel. The script
    determines which channel that currently is, then reports which channel flake.lock
    references, together with the revision it is locked to and how old that lock is.

Notes:
    Policy: nixos-unstable is not used. Reproducibility is carried by flake.lock, so
    the channel only decides what arrives when the lock is updated. A stable channel
    makes that arrival smaller and more predictable, which suits a verification
    meant to be reproduced.

    The latest stable channel is found through lib/.version rather than the branch
    list. The GitHub branches API pages at 100 entries, and nixpkgs exceeds that in
    protected branches alone, so a branch listing can miss the channel. Reading
    lib/.version settles in one request both whether a branch exists and which version
    it claims to be. master claims the version that will be released next, so the
    search walks back from there until a nixos-<version> branch exists and claims the
    same version.

    This script reads the network. A failure to read lib/.version on master, the
    one request this script cannot do without, including total unreachability,
    is reported as exit 3, not 1, so that a caller can distinguish "could not judge
    because the network failed" from "could not judge because a tool is missing".
    A 404 while walking back from master to find the latest released nixos-YY.MM
    branch is not treated as this failure: a channel that does not exist yet is
    the expected shape of that search, not an unreachable upstream.
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
# this apart from a missing tool or a genuine policy violation.
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

# ANCHOR: NixpkgsChannel
##############################################################################################
PROGRESS "$LINENO" "resolving the latest stable nixpkgs channel"

# Print lib/.version on the given branch. Fails when the branch does not exist;
# the caller decides whether that is an error.
channel_version() {
    curl --fail --silent "https://raw.githubusercontent.com/NixOS/nixpkgs/$1/lib/.version" 2>/dev/null
}

# Print the release number before the given one, stepping between .05 and .11
# (26.11 -> 26.05, 26.05 -> 25.11).
previous_release() {
    local year=${1%%.*}
    if [ "${1##*.}" = "11" ]; then
        printf '%s.05\n' "$year"
    else
        printf '%s.11\n' "$((year - 1))"
    fi
}

if ! master_version=$(channel_version master); then
    network_failure "reading lib/.version on nixpkgs master"
fi

candidate=$master_version
latest_stable=
i=0
while [ "$i" -lt 4 ]; do
    PROGRESS "$LINENO" "checking whether nixos-$candidate is released"

    if [ "$(channel_version "nixos-$candidate" || true)" = "$candidate" ]; then
        latest_stable="nixos-$candidate"
        break
    fi
    candidate=$(previous_release "$candidate")
    i=$((i + 1))
done

EMSG="line:$LINENO ERROR no released nixos-YY.MM channel found near $master_version."
[ -n "$latest_stable" ]

##############################################################################################
PROGRESS "$LINENO" "reading flake.lock in this repository"

# original.ref is the channel as requested; locked.* is what the lock resolved it to.
selected_ref=$(
    yq --input-format json --output-format yaml --exit-status --unwrapScalar \
        '.nodes.nixpkgs.original.ref' "$based/flake.lock"
)
locked_modified=$(
    yq --input-format json --output-format yaml --exit-status --unwrapScalar \
        '.nodes.nixpkgs.locked.lastModified' "$based/flake.lock"
)
locked_rev=$(
    yq --input-format json --output-format yaml --exit-status --unwrapScalar \
        '.nodes.nixpkgs.locked.rev' "$based/flake.lock"
)

##############################################################################################
PROGRESS "$LINENO" "judging the referenced channel"

case "$selected_ref" in
"$latest_stable")
    status=aligned
    ;;
nixos-unstable | nixos-unstable-small)
    status=unstable-channel
    ;;
nixos-*)
    status=update-available
    ;;
*)
    status=unexpected-ref
    ;;
esac

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
check: nixpkgs-channel
generated_at: "$stime"
result: $result
status: $status
expected_channel: "$latest_stable"
observed:
  nixpkgs_master_version: "$master_version"
  this_repository:
    channel: "$selected_ref"
    locked_rev: "$locked_rev"
    locked_date: "$(date -u -d "@$locked_modified" +%Y-%m-%d 2>/dev/null || echo unknown)"
    locked_age_days: $((($(date -u +%s) - locked_modified) / 86400))
EOF

################################################################
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
# ANCHOR_END: NixpkgsChannel

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
