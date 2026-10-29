# The entry point of the build of this repository (GNU make). Run outside the
# devshell, it runs the same goals again in it (scripts/restricted-devshell.sh),
# passing on the variables given on the command line.
#
# Run `make deps` (or any target that needs it) before building: lake build in
# a package of the verification builds Mathlib from source when its built
# files have not been fetched, which takes hours. The targets that build hold
# the lock .lake-build.lock, so that two builds in the same tree do not
# overlap; the second one waits for the first.

SHELL := bash
.SHELLFLAGS := -eu -o pipefail -c
.ONESHELL:
.DEFAULT_GOAL := help

code := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
lock := $(code)/.lake-build.lock

# The devshell of this repository sets SOFTFLOAT_CODE_SHELL, and the devshell of
# the audit repository, which has the same tools, sets SOFTFLOAT_AUDIT_SHELL.
ifeq ($(SOFTFLOAT_CODE_SHELL)$(SOFTFLOAT_AUDIT_SHELL),)
goals := $(or $(MAKECMDGOALS),$(.DEFAULT_GOAL))
.PHONY: $(goals)
$(firstword $(goals)):
	exec "$(code)/scripts/restricted-devshell.sh" make -C "$(code)" $(MAKEOVERRIDES) $(goals)
ifneq ($(words $(goals)),1)
$(wordlist 2,$(words $(goals)),$(goals)):
	@:
endif
else

# In the order of their requirements.
packages := core-operators riscv-operators core-verification riscv-verification
# The packages that require Mathlib.
verification := core-verification riscv-verification

# Take the lock on file descriptor 9 for the rest of the recipe, saying so
# when another build holds it.
define take-lock
exec 9>"$(lock)"
if ! flock -n 9; then
    echo "make: waiting for another build in $(code) to finish (lock $(lock))" >&2
    flock 9
fi
endef

.PHONY: help deps build check testfloat clean

help:
	@echo 'Targets (from code/ or with make -C code; outside the devshell, they run in it):'
	echo '  help       Print this list (the default target).'
	echo '  deps       Fetch the built Mathlib for core-verification and riscv-verification'
	echo '             (lake exe cache get), once for each revision of Mathlib in their'
	echo '             lake-manifest.json, and check that Mathlib.olean is there.'
	echo '  build      deps, then lake build in core-operators, riscv-operators,'
	echo '             core-verification and riscv-verification, in this order.'
	echo '  check      build, then scripts/check-claim-build.sh,'
	echo '             scripts/check-package-dependencies.sh and'
	echo '             scripts/check-testfloat-record.sh; stops at the first that fails.'
	echo '  testfloat  build, then run the comparison with TestFloat and write its record'
	echo '             again (riscv-verification/testfloat/scripts/record_testfloat_level1.sh).'
	echo '  clean      Remove what was built of the packages (.lake/build of each),'
	echo '             keeping the fetched Mathlib (.lake/packages).'
	echo 'Do not run lake build in a package of the verification before make deps:'
	echo 'without the built Mathlib, it builds Mathlib from source.'

# A mark .lake/mathlib-fetched.<rev> in each package records that the built
# Mathlib of that revision was fetched; with the mark and Mathlib.olean there,
# nothing is fetched again.
deps:
	@$(take-lock)
	for package in $(verification); do
	    dir=$(code)/$$package
	    rev=$$(jq -r '.packages[] | select(.name == "mathlib") | .rev' "$$dir/lake-manifest.json")
	    if [ -z "$$rev" ] || [ "$$rev" = null ]; then
	        echo "make: no revision of mathlib in $$dir/lake-manifest.json" >&2
	        exit 1
	    fi
	    mark=$$dir/.lake/mathlib-fetched.$$rev
	    olean=$$dir/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
	    if [ -e "$$mark" ] && [ -e "$$olean" ]; then
	        echo "make: the built Mathlib $$rev is already fetched in $$package"
	        continue
	    fi
	    echo "make: fetching the built Mathlib $$rev in $$package"
	    (cd "$$dir" && lake exe cache get)
	    if [ ! -e "$$olean" ]; then
	        echo "make: $$olean is missing after lake exe cache get; not building Mathlib from source" >&2
	        exit 1
	    fi
	    rm -f "$$dir"/.lake/mathlib-fetched.*
	    touch "$$mark"
	done

build: deps
	@$(take-lock)
	for package in $(packages); do
	    echo "make: lake build in $$package"
	    (cd "$(code)/$$package" && lake build)
	done

check: build
	@$(take-lock)
	cd "$(code)"
	scripts/check-claim-build.sh
	scripts/check-package-dependencies.sh
	scripts/check-testfloat-record.sh

testfloat: build
	@$(take-lock)
	"$(code)/riscv-verification/testfloat/scripts/record_testfloat_level1.sh"

clean:
	@$(take-lock)
	for package in $(packages); do
	    rm -rf "$(code)/$$package/.lake/build"
	done
endif
