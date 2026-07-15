#! -*- Makefile -*-

# --------------------------------------------------------------------
TAG       := ecbounds
WDIR      := /home/charlie
JOBS      ?= 2
SCENARIOS ?= eclib frodokem mlkem
DOCKER    := docker run --rm -m 12G -v ecbounds-data:$(WDIR)/out
DOCKERVOL := 

# --------------------------------------------------------------------
.PHONY: default build run runtest

default:
	@echo "usage: make [build|run|run-proofs|run-kyber|run-frodokem|run-extract-kyber|run-extract-frodokem]" >&2
	@exit 1

build:
	docker build -t $(TAG) .
	docker volume create ecbounds-data
	$(DOCKER) -w $(WDIR) -ti $(TAG) sh -c 'sudo chmod 777 /home/charlie/out && touch out/.keep'

run:
	$(DOCKER) -w $(WDIR) -ti $(TAG) \
	  /bin/bash

run-proofs:
	$(DOCKER) -w $(WDIR)/examples/proof -ti $(TAG) \
	  opam exec -- easycrypt runtest -jobs $(JOBS) \
	  tests.config $(SCENARIOS)

run-kyber:
	$(DOCKER) -w $(WDIR)/out -ti $(TAG) \
	  opam exec -- kyber-calculator

run-frodokem:
	$(DOCKER) -w $(WDIR)/out -ti $(TAG) \
	  opam exec -- frodo-calculator

run-extract-kyber:
	$(DOCKER) -w $(WDIR)/out -ti $(TAG) \
    jq -r '{ name: "Kyber1024", cucv: .estimate_cu_cv, cu: .estimate_cu, provable: (.provable.mintcu as $$mintcu | (.provable.alltcu[] | select(.[0]==$$mintcu)) | .[3]) }' kyber-1024.json
	$(DOCKER) -w $(WDIR)/out -ti $(TAG) \
    jq -r '{ name: "Kyber768", cucv: .estimate_cu_cv, cu: .estimate_cu, provable: (.provable.mintcu as $$mintcu | (.provable.alltcu[] | select(.[0]==$$mintcu)) | .[3]) }' kyber-768.json

run-extract-frodokem:
	$(DOCKER) -w $(WDIR)/out -ti $(TAG) \
    jq -r '.[] | { n: .n, failurepr: .failurepr}' frodokem.json

kill-docker:
	-docker kill $$(docker ps -q --filter ancestor=ecbounds) 
