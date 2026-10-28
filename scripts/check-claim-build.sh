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
    $pname - Judge whether the claims of Core and RISCV build, with the checks
    inside their builds, and whether the kernel accepts them again when they
    are replayed from what was built

Usage:
    $0

Inputs:
    - files
        - core-verification/ and riscv-verification/, and through their
          requirements core-operators/ and riscv-operators/
    - commands
        - lake
        - lean, for the prefix of the toolchain, whose bin/ holds leanexport
          and leanchecker
        - scripts/lean-env.sh, to run leanexport with every module on the
          search path

Outputs:
    A YAML record of the judgement on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  Both packages of the verification built, and the kernel accepted
           the replay of both claims. status: built.
        1  lake or lean is missing, the built Mathlib was not fetched (run
           make deps first; the check does not build Mathlib from source), or
           scripts/lean-env.sh could not set up the search path for the
           export (such as when a module is in two packages). No record of the
           judgement is written.
        4  The build of a package of the verification failed, or the kernel
           rejected the replay of a claim. status: failed. The last lines of
           the output of each build or replay that failed are in the record.

Description:
    The claims are SoftFloat.Core.Claim, in core-verification/, and
    SoftFloat.RISCV.Claim, in riscv-verification/; each package is built in its
    own directory with its default targets, which include the modules that
    import the claim and run its checks, SoftFloat.Core.Claim.Checked and
    SoftFloat.RISCV.Claim.Checked. The builds carry checks that run as part of
    them: in each of these modules, checkClaimStatements (the statements of
    the constants of the namespace of the claim whose types are propositions
    use only definitions of the layers allowed and the core of Lean) and
    checkClaimAxioms (those constants depend only on propext,
    Classical.choice and Quot.sound); in the specification of Core,
    SoftFloat.Spec.checkCoverage (the fields of Ops, Correct and Agree, and of
    FormatOps and FormatCorrect, agree, each field of Correct states its own
    operation alone, and each field of Agree states that the values of its
    operation of the two sets are equal); in the specification of RISCV,
    SoftFloat.RISCV.Spec.checkCoverage (the same for each of the four groups
    of instructions and its predicates of correctness and agreement) and
    SoftFloat.RISCV.Spec.checkOperationsCoverage (the same for RiscvOps,
    RiscvCorrect and RiscvAgree). A failure of any of them, or of a proof,
    makes the build fail.

    Then the two theorems of each claim are replayed through the kernel from
    what was built: leanexport writes them and every constant they depend on,
    down to the core of Lean, from the .olean files, and leanchecker
    --from-export adds that export to an empty environment of the kernel. It
    finds a declaration in the .olean files that the kernel never accepted,
    such as one added with debug.skipKernelTC or written into the environment
    by a program; the build alone cannot tell such a declaration apart, and
    checkClaimAxioms looks only at the axioms.

Notes:
    The first build after the sources changed can take minutes, since it
    builds the proofs. The replay takes some seconds for each claim.

    The four packages put their modules under the same root SoftFloat, and the
    search path of Lean (LEAN_PATH) finds a module only in the first entry
    that has the directory SoftFloat/. So \`lake env leanexport\` does not
    find the modules of the other packages. The export runs through
    scripts/lean-env.sh, which puts a tree of symbolic links to the .olean
    files of every entry that has SoftFloat/ at the head of the search path,
    so that one entry has them all.
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

for command_name in lake lean; do
    EMSG="line:$LINENO ERROR $command_name is required."
    command -v "$command_name" >/dev/null
done

##############################################################################################
PROGRESS "$LINENO" "checking that the built Mathlib was fetched"

# Without the built Mathlib, lake build builds Mathlib from source, which
# takes hours. make deps fetches it (lake exe cache get).
for package in core-verification riscv-verification; do
    EMSG="line:$LINENO ERROR the built Mathlib is not in $package/.lake/packages/mathlib; run make deps first."
    [ -e "$based/$package/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]
done

tmpd=$(mktemp -d -t "$pname.$stime.$$.XXXXXXXX")
trap 'rm -rf "$tmpd"' EXIT

##############################################################################################
# ANCHOR: ClaimBuildCheck
PROGRESS "$LINENO" "building the claims"

# The build failing is a judgement, not an error of this check. Core is built
# first, as the verification of RISCV requires it.
status=built
code=0
: >"$tmpd/packages"
for package in core-verification riscv-verification; do
    if (cd "$based/$package" && lake build) >"$tmpd/build.$package" 2>&1; then
        printf '%s\tbuilt\n' "$package" >>"$tmpd/packages"
    else
        printf '%s\tfailed\n' "$package" >>"$tmpd/packages"
        status=failed
        code=4
    fi
done

PROGRESS "$LINENO" "replaying the claims through the kernel"

# Only what built is replayed. A rejection is a judgement, as a failing build.
: >"$tmpd/replays"
if [ "$status" = built ]; then
    bin=$(lean --print-prefix)/bin
    while read -r package module theorems; do
        exported=0
        # The theorems are split into words on purpose.
        # shellcheck disable=SC2086
        "$based/scripts/lean-env.sh" "$based/$package" "$bin/leanexport" "$module" -- $theorems \
            >"$tmpd/export.$package" 2>"$tmpd/replay.$package" || exported=$?
        # 125 is a failure of lean-env.sh itself, such as a module found in two
        # places: an error of this check, not a judgement.
        if [ "$exported" = 125 ]; then
            cat "$tmpd/replay.$package" >&3
            EMSG="line:$LINENO ERROR scripts/lean-env.sh failed for $package."
            false
        fi
        if [ "$exported" = 0 ] &&
            "$bin/leanchecker" --from-export "$tmpd/export.$package" >>"$tmpd/replay.$package" 2>&1; then
            printf '%s\taccepted\n' "$package" >>"$tmpd/replays"
        else
            printf '%s\trejected\n' "$package" >>"$tmpd/replays"
            status=failed
            code=4
        fi
    done <<EOF
core-verification SoftFloat.Core.Claim SoftFloat.Claim.correctness SoftFloat.Claim.uniqueness
riscv-verification SoftFloat.RISCV.Claim SoftFloat.RISCV.Claim.correctness SoftFloat.RISCV.Claim.uniqueness
EOF
fi

PROGRESS "$LINENO" "writing the record"

# The last lines of the output of each build that failed.
while IFS=$'\t' read -r package state; do
    [ "$state" = failed ] || continue
    jq -R -s --arg package "$package" '{($package): (split("\n") | map(select(. != "")) | .[-20:])}' "$tmpd/build.$package"
done <"$tmpd/packages" >"$tmpd/tails"
# The last lines of the output of each replay that the kernel rejected.
while IFS=$'\t' read -r package state; do
    [ "$state" = rejected ] || continue
    jq -R -s --arg package "$package" '{($package): (split("\n") | map(select(. != "")) | .[-20:])}' "$tmpd/replay.$package"
done <"$tmpd/replays" >"$tmpd/replay-tails"
jq -n \
    --arg generated_at "$stime" \
    --arg status "$status" \
    --argjson result "$([ "$code" = 0 ] && echo true || echo false)" \
    --rawfile packages "$tmpd/packages" \
    --rawfile replays "$tmpd/replays" \
    --slurpfile tails "$tmpd/tails" \
    --slurpfile replay_tails "$tmpd/replay-tails" '
    def table: split("\n") | map(select(. != "") | split("\t") | {(.[0]): .[1]}) | add;
    {check: "claim-build", generated_at: $generated_at, result: $result, status: $status,
     packages: ($packages | table)}
    + (if $replays != "" then {kernel_replay: ($replays | table)} else {} end)
    + (if $tails != [] then {build_tail: ($tails | add)} else {} end)
    + (if $replay_tails != [] then {replay_tail: ($replay_tails | add)} else {} end)
    ' |
yq -P '.'
exit "$code"
# ANCHOR_END: ClaimBuildCheck

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
