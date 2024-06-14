ISADK_DIR ?= ../..

.SUFFIXES:

DK_FILES := $(wildcard *.dk)
V_FILES := $(DK_FILES:%.dk=%.v)
VO_FILES := $(V_FILES:%.v=%.vo)

.PHONY: default
default: vo

.PHONY: clean-dk
clean-dk:
	find . -maxdepth 1 -name '*.dk' -a ! -name STTfa.dk -delete
	find . -maxdepth 1 -name '*.sh' -a ! -name dkcheck_STTfa.sh -delete

.PHONY: clean-dko
clean-dko:
	find . -maxdepth 1 -name '*.dko' -delete

.PHONY: clean-lp
clean-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name STTfa.lp -delete

.PHONY: clean-lpo
clean-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: v
v: $(V_FILES)

LAMBDAPI ?= lambdapi

#SESSION := $(shell awk -f $(ISADK_DIR)/session.awk _CoqProject)

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --renaming $(ISADK_DIR)/renaming.lp --requiring Isabelle.v --no-implicits $*.dk | sed -e 's/^Require Import Isabelle./From IsaCoq Require Import Isabelle./' > $*.v

.PHONY: clean-v
clean-v:
	find . -maxdepth 1 -name '*.v' -a ! -name Isabelle.v -delete

_CoqProject: $(V_FILES)
	touch $@

coq.mk: _CoqProject
	coq_makefile -f $< -o $@

MAKE_COQ := $(MAKE) -f coq.mk

.PHONY: vo
vo: coq.mk $(V_FILES)
	$(MAKE_COQ)
#vo: $(VO_FILES)

.PHONY: clean-vo
clean-vo:
	find . -maxdepth 1 -name '*.vo*' -delete
	find . -maxdepth 1 -name '*.glob' -delete
	find . -maxdepth 1 -name '.*.aux' -delete
	rm -f .lia.cache .nia.cache

.PHONY: clean-all
clean-all: clean-dk clean-dko clean-lp clean-lpo clean-v clean-vo
	-rm -f coq.mk coq.mk.conf
#	-rm -f deps.mk

#%.vo: coq.mk %.v
#	$(MAKE_COQ) $*.vo

#%.vo: %.v
#	@echo coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<
#	@coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<

#include deps.mk

#deps.mk:
#	$(ISADK_DIR)/coqdeps.sh > $@
