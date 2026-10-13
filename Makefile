JOBS        ?= 4
MPFR_PREFIX ?=

PROOF_DIR := examples/proof
CALC_DIR  := examples/bound-calculator
OUT_DIR   := out

ifneq ($(MPFR_PREFIX),)
export CPATH           := $(MPFR_PREFIX)/include$(if $(CPATH),:$(CPATH))
export LIBRARY_PATH    := $(MPFR_PREFIX)/lib$(if $(LIBRARY_PATH),:$(LIBRARY_PATH))
export LD_LIBRARY_PATH := $(MPFR_PREFIX)/lib$(if $(LD_LIBRARY_PATH),:$(LD_LIBRARY_PATH))
endif

.PHONY: help check proofs bounds check-bounds versions clean

help:
	@echo "usage: make <target> [JOBS=n] [MPFR_PREFIX=dir]"
	@echo ""
	@echo "  check         proofs + bounds + check-bounds"
	@echo "  proofs        check all EasyCrypt proofs from scratch"
	@echo "  bounds        build and run the bound calculator (writes $(OUT_DIR)/kaiburr-*.json)"
	@echo "  check-bounds  check every bound admitted in the proofs against the calculator output"
	@echo "  versions      print the toolchain versions in use"
	@echo "  clean         remove all build outputs"
	@echo ""
	@echo "  JOBS          parallel EasyCrypt jobs (default $(JOBS))"
	@echo "  MPFR_PREFIX   install prefix of MPFR >= 4.2.1, if not the system one"

check: proofs bounds check-bounds

proofs:
	find $(PROOF_DIR) -name '*.eco' -delete
	cd $(PROOF_DIR) && easycrypt runtest -jobs $(JOBS) tests.config eclib mlkem

bounds:
	cd $(CALC_DIR) && dune build --root . ./kyber.exe
	mkdir -p $(OUT_DIR)
	cd $(OUT_DIR) && $(CURDIR)/$(CALC_DIR)/_build/default/kyber.exe

check-bounds:
	python3 scripts/check-bounds.py --out $(OUT_DIR) --proofs $(PROOF_DIR)/mlkem --calculator $(CALC_DIR)/kyber.ml

versions:
	@easycrypt config 2>&1 | grep -E "^git-hash|^known provers"
	@printf "ocaml: "; ocaml -vnum
	@printf "mlmpfr: "; opam show mlmpfr --field=version 2>/dev/null || echo "not installed"
	@python3 --version

clean:
	find $(PROOF_DIR) -name '*.eco' -delete
	rm -rf $(CALC_DIR)/_build $(CALC_DIR)/kyber.exe $(OUT_DIR)
