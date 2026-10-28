#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status

stime=$(date -u +%Y%m%dT%H%M%SZ)
based=$(cd -- "$(dirname -- "$0")/.." && pwd)
pname=$(basename -- "$0")

print_help() {
    cat <<EOF
Name:
    $pname - Enter restricted development shell or execute a command within it

Usage:
    $0
        - Enter restricted development shell
    $0 make build
        - Execute the specified command within the restricted development shell

Inputs:
    - files
        - flake.nix
        - flake.lock.
    - environment variables
        - HOME
        - TERM

Outputs:
    The exit code of the executed command.

Description:
    Enter a restricted development shell where only the tools fixed by flake.lock are
    available, and host environment settings are not carried over, except HOME and TERM
    which elan and interactive use require.
    This ensures that the development environment is consistent and reproducible,
    independent of the host system's configuration.

Notes:
    nix drops some variables when it writes out the development environment: those
    named in ignoreVars in nix's src/nix/develop.cc. That keeps nix from clobbering
    the caller's own values, but under --ignore-environment the caller has no values
    either, so those variables end up unset rather than pinned. This script restores
    three of them:

        HOME           Kept from the caller, because elan stores toolchains in ~/.elan.
        TERM           Kept from the caller, so that the terminal stays usable.
        SSL_CERT_FILE  Always assigned from NIX_SSL_CERT_FILE, the cacert pinned by the
                       flake, for tools that read only this variable (git, Python,
                       rustls). The caller cannot override it: this script fixes the
                       list of variables passed to --keep, so no value reaches here.

    Removal condition: in ignoreVars, SSL_CERT_FILE carries the comment
    "FIXME: only want to ignore /no-cert-file.crt" and HOME carries
    "FIXME: don't ignore in pure mode?". Once nix fixes those, the corresponding
    lines here are no longer needed.

    Two further adjustments are made for reasons unrelated to ignoreVars:

        LANG           Set to C.UTF-8 rather than taken from the caller. Otherwise the
                       locale falls back to POSIX, and paths that contain non-ASCII
                       characters are mishandled.
        Startup files  The interactive shell is started with --norc --noprofile. HOME is
                       kept, so bash would otherwise read the host's startup files and
                       carry host settings into the restricted environment.
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

##############################################################################################
PROGRESS "$LINENO" "checking arguments"

case "${1:-}" in
-h | --help)
    print_help
    exit 0
    ;;
esac

##############################################################################################
PROGRESS "$LINENO" "invoking restricted nix devshell"

# The shell is replaced on purpose: the exit code of the command belongs to the
# caller, and the single quotes keep the inner shell's expansions for the inner shell.
# shellcheck disable=SC2093,SC2016
exec nix develop "$based" \
    --ignore-environment \
    --keep HOME \
    --keep TERM \
    --command bash -c '
        export SSL_CERT_FILE="$NIX_SSL_CERT_FILE"
        export LANG=C.UTF-8
        if [ "$#" -eq 0 ]; then
            export PS1="(restricted) \W\\$ "
            exec bash --norc --noprofile
        else
            exec "$@"
        fi
    ' restricted-devshell "$@"

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
