ISADK_DIR ?= ../..

.SUFFIXES:

DK_FILES := $(wildcard *.dk)
V_FILES := $(DK_FILES:%.dk=%.v)
VO_FILES := $(V_FILES:%.v=%.vo)

.PHONY: default
default: vo

.PHONY: v
v: $(V_FILES)

LAMBDAPI ?= lambdapi

#SESSION := $(shell awk -f $(ISADK_DIR)/session.awk _CoqProject)

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --renaming $(ISADK_DIR)/renaming.lp --requiring Isabelle.v --no-implicits $*.dk | sed -e 's/^Require Import Isabelle./From IsaCoq Require Import Isabelle./' > $*.v

.PHONY: clean-v
clean-v:
	-rm -f $(V_FILES)

coq.mk: _CoqProject
	coq_makefile -f _CoqProject -o coq.mk

MAKE_COQ := $(MAKE) -f coq.mk

.PHONY: vo
vo: coq.mk $(V_FILES)
	$(MAKE_COQ)
#vo: $(VO_FILES)

.PHONY: clean-vo
clean-vo:
	$(MAKE_COQ) clean
	#-rm -f *.vo *.vok *.vos *.glob

.PHONY: clean
clean: clean-v clean-vo
#	-rm -f deps.mk
#	-rm -f coq.mk coq.mk.conf

#%.vo: coq.mk %.v
#	$(MAKE_COQ) $*.vo

#%.vo: %.v
#	@echo coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<
#	@coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<

#include deps.mk

#deps.mk:
#	$(ISADK_DIR)/coqdeps.sh > $@
