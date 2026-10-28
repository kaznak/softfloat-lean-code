#!/bin/bash

set -C # noclobber: prevent overwriting files with redirection
set -u # treat unset variables as an error and exit immediately
set -e # exit immediately if a command exits with a non-zero status
set -o pipefail # return the status of the last command in the pipe that failed
set -E # let functions and subshells inherit the ERR trap

stime=$(date -u +%Y%m%dT%H%M%SZ)
pname=$(basename -- "$0")

# The root of the names of the modules that the packages of this repository
# share.
root=SoftFloat

print_help() {
    cat <<EOF
Name:
    $pname - Run a command in the environment of a Lake package, with every
    module under $root/ found on the search path of Lean

Usage:
    $0 <package> <command> [<argument>...]

    <package> is the directory of any Lake package whose dependencies include
    the packages of this repository: a package of this repository, such as
    riscv-verification/, or a project of a user that requires one of them,
    from git or from a path. Build it first (make build in this repository,
    lake build in a project of a user); this script builds nothing. The
    command runs in the current directory, so the paths in its arguments are
    relative to where the caller stands.

    Examples, from the top of this repository:

        $0 riscv-verification lean Try.lean
        $0 riscv-verification lean --deps Try.lean
        $0 riscv-verification leanchecker SoftFloat.RISCV.Claim
        $0 riscv-verification leanexport SoftFloat.RISCV.Claim >claim.export

    In a project of a user that requires softfloat-riscv-operators from git,
    the clone of this repository is under .lake/packages/, and from the top
    of the project:

        .lake/packages/softfloat-riscv-operators/scripts/$pname . lean Main.lean

Inputs:
    - files
        - the .olean files and the sources under $root/ of the packages on
          the search paths of <package>, as Lake reports them
    - commands
        - lake, to read the search paths and to run the command in the
          environment of the package
        - <command>

Outputs:
    The output of the command. The exit code is the exit code of the command.
    When this script itself fails (a missing tool, a package that Lake cannot
    read, or a module found in two places), it writes the reason on standard
    error and exits with 125, without running the command.

Description:
    The packages of this repository put their modules under the same root
    $root. Lake builds them, and elaborates a file with lake lean and in the
    editor, finding the package of each module itself. But the search path of
    Lean (LEAN_PATH and LEAN_SRC_PATH) finds a module only in the first entry
    that has the directory of its root, $root/, and does not go on to the next
    entry; so a tool that finds modules through it (lean on a file,
    lean --deps and --src-deps, leanchecker, leanexport) does not find the
    modules of the second package and after.

    This script asks Lake for the search paths of <package>
    (lake env printenv LEAN_PATH and LEAN_SRC_PATH), gathers symbolic links
    to the $root/ of every entry that has one into one tree in a temporary
    directory, one tree for the .olean files and another for the sources,
    puts each tree at the head of its search path, runs the command in the
    environment of the package (lake env), removes the trees, and returns the
    exit code of the command. The other entries stay on the search paths
    after the trees.

    A module is named by the path of its files under the entry without their
    extensions. If one module is in two entries, the script stops before
    running the command and names the module and the entries, instead of
    choosing one of them. Lake itself refuses such a pair when it builds.

Notes:
    The paths that lean --deps and --src-deps print for the modules under
    $root/ are in the trees, which are removed when the command ends;
    readlink -f gives the file behind each while the command runs.

    lake check, lake lint and lake shake set the search path themselves, and
    do not take the one this script sets. The README of this repository
    describes the way around for lake check, and what has none.
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
    exit 125
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

EMSG="line:$LINENO ERROR a package and a command are required; see --help."
[ "$#" -ge 2 ]
package=$1
shift

EMSG="line:$LINENO ERROR $package is not a directory."
[ -d "$package" ]

EMSG="line:$LINENO ERROR lake is required."
command -v lake >/dev/null

tmpd=$(mktemp -d -t "$pname.$stime.$$.XXXXXXXX")
trap 'rm -rf "$tmpd"' EXIT

##############################################################################################
# ANCHOR: LeanEnv
PROGRESS "$LINENO" "reading the search paths of the package"

# In the directory of the package, so that a lake of elan picks the toolchain
# of the package. LAKE is the lake of that toolchain itself, which runs the
# command below from the directory of the caller.
for variable in LAKE LEAN_PATH LEAN_SRC_PATH; do
    (cd "$package" && lake env printenv "$variable") >"$tmpd/$variable"
done

PROGRESS "$LINENO" "gathering the modules under SoftFloat into one tree"

# One tree for each search path: olean for LEAN_PATH, src for LEAN_SRC_PATH.
for kind in olean src; do
    case "$kind" in
    olean) variable=LEAN_PATH ;;
    src) variable=LEAN_SRC_PATH ;;
    esac
    # The entries that have the root, each once, in their order.
    tr ':' '\n' <"$tmpd/$variable" |
    while read -r entry; do
        [ -n "$entry" ] && [ -d "$entry/$root" ] && realpath -- "$entry"
        :
    done |
    awk '!seen[$0]++' >"$tmpd/entries.$kind"
    # Each module with the entry that has it: the path of a file under the
    # entry, without everything from the first dot of its name.
    while read -r entry; do
        (cd "$entry" && find "$root" ! -type d) |
        sed 's#\.[^/]*$##' |
        awk -v entry="$entry" '{print $0 "\t" entry}'
    done <"$tmpd/entries.$kind" |
    sort -u >"$tmpd/modules.$kind"
    awk -F '\t' '{count[$1]++} count[$1] == 2 {print $1}' "$tmpd/modules.$kind" >"$tmpd/duplicates.$kind"
    if [ -s "$tmpd/duplicates.$kind" ]; then
        awk -F '\t' 'NR == FNR {duplicate[$1] = 1; next} duplicate[$1] {print}' \
            "$tmpd/duplicates.$kind" "$tmpd/modules.$kind" |
        while IFS=$'\t' read -r module entry; do
            MSG "line:$LINENO ERROR the module ${module//\//.} is in $entry."
        done
        EMSG="line:$LINENO ERROR a module is in two entries of $variable of $package."
        false
    fi
    mkdir "$tmpd/$kind"
    while read -r entry; do
        cp -rs "$entry/$root" "$tmpd/$kind/"
    done <"$tmpd/entries.$kind"
done

PROGRESS "$LINENO" "running the command"

# The exit code of the command is the result, not an error of this script.
code=0
"$(cat "$tmpd/LAKE")" -d "$package" env env \
    LEAN_PATH="$tmpd/olean:$(cat "$tmpd/LEAN_PATH")" \
    LEAN_SRC_PATH="$tmpd/src:$(cat "$tmpd/LEAN_SRC_PATH")" \
    "$@" || code=$?
exit "$code"
# ANCHOR_END: LeanEnv

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
