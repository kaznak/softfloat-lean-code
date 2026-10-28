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
    $pname - Judge whether each target of this repository has its operators
    and its verification as separate packages, and whether the packages and
    the layers depend on each other only in the directions allowed

Usage:
    $devshell $0

Inputs:
    - files
        - <target>-operators/lakefile.toml and
          <target>-verification/lakefile.toml (core-operators/,
          core-verification/, riscv-operators/ and riscv-verification/), and
          the absence of lakefile.lean there
        - the .lean files of those packages, built here
        - scripts/package-dependencies.yaml: the rules, each with the
          constraints it places on the dependencies
    - commands
        - lake, to build the packages, and lean, to run
          scripts/module-imports.lean on what was built

Outputs:
    A YAML record of the judgement on standard output. It carries result,
    which every check reports, and status, which says how it came out. The exit
    code is one of:

        0  Each target has its operators and its verification as packages of
           their own, every module is in a layer of its package, and every
           require and every import goes in a direction allowed.
           status: layered.
        1  A lakefile.toml could not be read, the built Mathlib was not
           fetched (run make deps first; the check does not build Mathlib from
           source), a package did not build, or a tool is missing. No record
           is written, because nothing was judged.
        2  Some package is missing or not separate, some module is in no
           layer of its package, or some require or import goes against the
           directions allowed; the record lists each violation with the
           rule it breaks. status: violated.

Description:
    The packages are the directories at the top of the repository named
    <target>-operators and <target>-verification, and each is named
    softfloat-<directory>. The operators hold the layers Base and Operators of
    their target, the verification the layers Spec, Proof, Claim and Test. A
    module belongs to the layer its name starts with, SoftFloat.<Target>.<Layer>,
    and the layer is named <target>-<layer> in lower case (core-spec,
    riscv-test and so on).

    Two graphs are judged. The graph of the packages is made of the
    [[require]] entries of each lakefile.toml: a require with a path is
    resolved, relative to its package, to one of the packages; a require named
    mathlib with the git repository of Mathlib 4 (or the Reservoir scope
    leanprover-community) is Mathlib; any other require is something else.
    The graph of the layers is made of the imports of the modules, read from
    what Lean built (scripts/module-imports.lean), not from the text of the
    sources: a module of SoftFloat reaches the layer of the module it imports,
    a module of Mathlib is Mathlib, and the modules of Lean itself (Init, Std,
    Lean, Lake) are left out. Lake keeps the directions between packages, but
    nothing in Lean or Lake keeps them between the modules of one package, so
    the layers are judged here.

    Both graphs are judged against the constraints the rules of
    scripts/package-dependencies.yaml place on them (the property dependencies
    of a rule), each under the name of a package (softfloat-core-operators and
    so on) or of a layer (core-spec and so on): requires, what it must require
    or import directly; only, that those are all it requires or imports
    directly; forbids, what it must not reach, directly or through the
    transitive closure of its graph. A violation names the rule whose
    constraint it breaks.

Notes:
    It reads no network. It builds the packages, which takes minutes after the
    proofs changed and seconds otherwise. A path is resolved by its text, not
    through symbolic links. The dependencies of Mathlib itself are not
    followed: Mathlib cannot depend on the packages of this repository.
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
PROGRESS "$LINENO" "checking required commands"

for command_name in yq jq lake lean; do
    EMSG="line:$LINENO ERROR $command_name is required; run this script through $devshell."
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

# ANCHOR: PackageDependencies
##############################################################################################
PROGRESS "$LINENO" "listing the packages"

# Lake reads lakefile.lean in preference to lakefile.toml, so a lakefile.lean
# would hold requires this check does not see.
find "$based" -mindepth 2 -maxdepth 2 -type f \( -name lakefile.toml -o -name lakefile.lean \) -printf '%P\n' |
    jq -R -s '
    split("\n") | map(select(. != "") | split("/") | {package: .[0], file: .[1]})
    | map(select(.package | test("^[a-z0-9]+-(operators|verification)$")))
    ' >"$tmpd/configs.json"

EMSG="line:$LINENO ERROR no package was found."
[ "$(jq length "$tmpd/configs.json")" -gt 0 ]

##############################################################################################
PROGRESS "$LINENO" "reading the requires of each package"

: >"$tmpd/packages"
jq -r --arg based "$based" '.[] | select(.file == "lakefile.toml") | "\($based)/\(.package)/lakefile.toml"' "$tmpd/configs.json" |
    xargs -r -d '\n' yq -p toml -o json -I0 '{"file": filename, "name": .name, "require": (.require // [])}' >>"$tmpd/packages"

##############################################################################################
PROGRESS "$LINENO" "reading the constraints the rules place on the dependencies"

yq -o json -I0 '.' "$based/scripts/package-dependencies.yaml" |
    jq '[ .[] | select(.dependencies) | .rule as $r | .dependencies | to_entries[] | {key: .key, rule: $r} + .value ]' \
    >"$tmpd/constraints.json"

EMSG="line:$LINENO ERROR no rule places a constraint on the dependencies."
[ "$(jq length "$tmpd/constraints.json")" -gt 0 ]

##############################################################################################
PROGRESS "$LINENO" "building the packages"

# The imports are read from what Lean built, so a package that does not build
# leaves nothing to judge. The tail of its output goes to the terminal.
jq -r '.[] | select(.file == "lakefile.toml") | .package' "$tmpd/configs.json" >"$tmpd/package-dirs"
cat "$tmpd/package-dirs" |
while read -r package; do
    PROGRESS "$LINENO" "building $package"
    if ! (cd "$based/$package" && lake build) >"$tmpd/build.$package" 2>&1; then
        tail -n 20 "$tmpd/build.$package" >&3
        EMSG="line:$LINENO ERROR $package did not build."
        false
    fi
done

##############################################################################################
PROGRESS "$LINENO" "reading the imports of the modules as built"

# Each .lean file of a package is a module, named by its path; its .olean is
# where Lake builds it. A file without its .olean is built by no library of
# the package, so its imports cannot be read.
cat "$tmpd/package-dirs" |
while read -r package; do
    (cd "$based/$package" && find . -name .lake -prune -o -type f -name '*.lean' ! -name lakefile.lean -printf '%P\n') |
    LC_ALL=C sort |
    while read -r file; do
        module=${file%.lean}
        olean=$based/$package/.lake/build/lib/lean/$module.olean
        state=missing
        [ -f "$olean" ] && state=built
        printf '%s\t%s\t%s\t%s\n' "${module//\//.}" "$package" "$olean" "$state"
    done
done >"$tmpd/modules.tsv"

awk -F '\t' '$4 == "built" {print $1 "\t" $3}' "$tmpd/modules.tsv" >"$tmpd/oleans.tsv"
(cd "$based" && lean --run scripts/module-imports.lean "$tmpd/oleans.tsv") >"$tmpd/imports.tsv"

jq -R -s 'split("\n") | map(select(. != "") | split("\t") | {module: .[0], package: .[1], built: (.[3] == "built")})' \
    "$tmpd/modules.tsv" >"$tmpd/modules.json"
jq -R -s 'split("\n") | map(select(. != "") | split("\t") | {module: .[0], import: .[1]}) | unique' \
    "$tmpd/imports.tsv" >"$tmpd/imports.json"

##############################################################################################
PROGRESS "$LINENO" "judging the packages and the directions of their dependencies"

jq -n \
    --arg based "$based/" \
    --slurpfile configs "$tmpd/configs.json" \
    --slurpfile packages "$tmpd/packages" \
    --slurpfile constraints "$tmpd/constraints.json" \
    --slurpfile modules "$tmpd/modules.json" \
    --slurpfile imports "$tmpd/imports.json" '
    "separate-operators-and-verification-packages-for-each-target" as $separate
    | ([ $configs[0][].package ] | unique) as $dirs
    # A path resolved by its text, from the directory of its package.
    | def resolve($from):
        ($from + "/" + .) | split("/")
        | reduce .[] as $s ([]; if $s == "" or $s == "." then . elif $s == ".." then (if length > 0 then .[:-1] else ["..", .[]] end) else . + [$s] end)
        | join("/");
    def mathlib_git: test("^https://github\\.com/leanprover-community/mathlib4(\\.git)?/?$");
    # The layer of a module: SoftFloat.<Target>.<Layer>... is <target>-<layer>.
    def layer: split(".") as $c
        | if ($c | length) >= 3 and $c[0] == "SoftFloat" then "\($c[1] | ascii_downcase)-\($c[2] | ascii_downcase)" else null end;
    # The package a layer belongs to: Base and Operators are on the side of the
    # operators, Spec, Proof, Claim and Test on the side of the verification.
    def home: (capture("^(?<t>[a-z0-9]+)-(?<l>[a-z0-9]+)$") // null)
        | if . == null then null
          elif .l | IN("base", "operators") then "\(.t)-operators"
          elif .l | IN("spec", "proof", "claim", "test") then "\(.t)-verification"
          else null end;
    # What an import reaches: a layer, Mathlib, nothing (Lean itself) or something else.
    def reached: (split(".")[0]) as $r
        | if $r | IN("Init", "Std", "Lean", "Lake") then null
          elif $r == "Mathlib" then "mathlib"
          elif $r == "SoftFloat" and layer != null and (layer | home) != null then layer
          else "other:\(.)" end;
    def closure($direct):
        def reach($seen):
            ([ $seen[] as $s | ($direct[$s] // [])[] ] + $seen | unique) as $n
            | if $n == $seen then $n else reach($n) end;
        $direct | with_entries(.value = reach(.value));
    def v($at; $rule; $text): {at: $at, rule: $rule, text: $text};

    ($packages | map({key: (.file | ltrimstr($based) | split("/")[0]), value: .name}) | from_entries) as $name_of
    | ($packages | map((.file | ltrimstr($based) | split("/")[0]) as $d
        | {key: .name, value: {directory: $d, requires: [ .require[] | {name: .name, target: (
            if .path then (.path | resolve($d)) as $p | if $name_of[$p] then $name_of[$p] else "path:\($p)" end
            elif .name == "mathlib" and ((.git // "" | mathlib_git) or (.git == null and .scope == "leanprover-community")) then "mathlib"
            else "other:\(.name)" end) } ]}})
        | from_entries) as $pk
    | ($pk | map_values([ .requires[].target ] | unique)) as $pdirect
    | closure($pdirect) as $pclosure
    | ($modules[0] | map({key: .module, value: (.module | layer)}) | from_entries) as $layer_of
    | ([ $modules[0][] | .module | layer | select(. != null and home != null) ] | unique) as $layers
    | ([ $imports[0][] | ($layer_of[.module] // null) as $from | (.import | reached) as $to
         | select($from != null and $to != null and $from != $to) | {from: $from, to: $to} ]
       | group_by(.from) | map({key: .[0].from, value: (map(.to) | unique)}) | from_entries) as $imported
    | ([ $layers[] | {key: ., value: ($imported[.] // [])} ] | from_entries) as $ldirect
    | closure($ldirect) as $lclosure
    | [
        # Each target has its operators and its verification as packages of
        # their own, each named after its directory.
        ($dirs[] as $d
         | ([ $configs[0][] | select(.package == $d) | .file ]) as $files
         | if ($files | index("lakefile.toml")) == null then v($d; $separate; "\($d)/ has no lakefile.toml") else empty end,
           if ($files | index("lakefile.lean")) then v($d; $separate; "\($d)/ has a lakefile.lean, which Lake reads instead of lakefile.toml") else empty end,
           if $name_of[$d] and $name_of[$d] != "softfloat-\($d)" then v($d; $separate; "\($d)/ is named \($name_of[$d]), not softfloat-\($d)") else empty end),
        ([ $dirs[] | capture("^(?<t>.*)-(operators|verification)$").t ] | unique[] as $t
         | ("operators", "verification") as $side
         | select($dirs | index("\($t)-\($side)") | not)
         | v("\($t)-\($side)"; $separate; "the target \($t) has no package \($t)-\($side)/")),
        ([ $packages[] | .name ] | group_by(.)[] | select(length > 1)
         | v("*"; $separate; "more than one package is named \(.[0])")),
        ($pk | to_entries[] | .key as $p | .value.requires[]
         | if (.target | startswith("path:")) then
             v($p; $separate; "the require \(.name) points to \(.target | ltrimstr("path:")), which is none of the packages")
           elif $pk[.target] != null and .name != .target then
             v($p; $separate; "the require \(.name) points to the package \(.target)")
           else empty end),
        # Every module is built and is in a layer of its package.
        ($modules[0][]
         | (.module | layer) as $l
         | if (.built | not) then v(.package; $separate; "\(.module) is built by no library of \(.package), so its imports cannot be judged")
           elif $l == null or ($l | home) == null then v(.package; $separate; "\(.module) is not under SoftFloat.<Target>.<Layer> of a layer")
           elif ($l | home) != .package then v(.package; $separate; "\(.module) is in the layer \($l), which belongs to \($l | home)/, not \(.package)/")
           else empty end),
        # The constraints of the rules, each judged on its package or layer.
        ($constraints[0][] | . as $k
         | ($k.key | startswith("softfloat-")) as $is_package
         | (if $is_package then $pdirect else $ldirect end) as $direct
         | (if $is_package then $pclosure else $lclosure end) as $reach
         | (if $is_package then "require" else "import" end) as $verb
         | if $direct[$k.key] == null then
             v($k.key; $k.rule; "\($k.key) is constrained, but there is no such \(if $is_package then "package" else "layer" end)")
           else
             (($k.requires // [])[] | select(. as $t | $direct[$k.key] | index($t) | not)
              | v($k.key; $k.rule; "\($k.key) does not \($verb) \(.)")),
             (select($k.only) | ($direct[$k.key] - ($k.requires // [])) | select(length > 0)
              | v($k.key; $k.rule; "\($k.key) \($verb)s [\(join(", "))] besides [\(($k.requires // []) | join(", "))], which are all it may \($verb)")),
             (($k.forbids // [])[] | select(. as $t | $reach[$k.key] | index($t))
              | v($k.key; $k.rule; "\($k.key) depends on \(.), directly or through others"))
           end)
      ] as $violations
    | {packages: $pk, packages_depend_on: $pclosure, layers_import: $ldirect, layers_depend_on: $lclosure, violations: $violations}
    ' >"$tmpd/judgement.json"

##############################################################################################
PROGRESS "$LINENO" "printing the report"

jq --arg stime "$stime" '
    (.violations | length == 0) as $ok
    | {check: "package-dependencies", generated_at: $stime, result: $ok,
       status: (if $ok then "layered" else "violated" end),
       violations: .violations, packages: .packages, packages_depend_on: .packages_depend_on,
       layers_import: .layers_import, layers_depend_on: .layers_depend_on}
    ' "$tmpd/judgement.json" | yq -p json -o yaml '.'

##############################################################################################
PROGRESS "$LINENO" "exiting"

if [ "$(jq '.violations | length' "$tmpd/judgement.json")" -eq 0 ]; then
    exit 0
fi
exit 2
# ANCHOR_END: PackageDependencies

##############################################################################################
# Reached only if a command above that must not return does return.
# shellcheck disable=SC2317
EMSG="line:$LINENO FATAL unreachable code."
# shellcheck disable=SC2317
false
