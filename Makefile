.SUFFIXES:

DK_FILES := $(wildcard *.dk)
V_FILES := $(DK_FILES:%.dk=%.v)
VO_FILES := $(DK_FILES:%.dk=%.vo)

.PHONY: default
default: vo

.PHONY: v
v: $(V_FILES)

LAMBDAPI ?= lambdapi

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --requiring Isabelle.v --no-implicits $*.dk | sed -e 's/^Require Import Isabelle./From IsaCoq Require Import Isabelle./' -e 's/^Require STTfa./From DkLogic Require STTfa./' -e 's/^Require Pure./From Pure Require Pure./' -e 's/^Require /From HOL_wp Require /' > $*.v

.PHONY: clean-v
clean-v:
	-rm -f $(V_FILES)

#Makefile.coq: _CoqProject
#	coq_makefile -f _CoqProject -o Makefile.coq

#MAKE_COQ := $(MAKE) -f Makefile.coq

.PHONY: vo
#vo: Makefile.coq $(V_FILES)
#	$(MAKE_COQ)
vo: $(VO_FILES)

.PHONY: clean-vo
clean-vo:
	-rm -f *.vo *.vok *.vos *.glob

.PHONY: clean
clean: clean-v clean-vo
	-rm -f deps.mk
#	-rm -f Makefile.coq Makefile.coq.conf

#%.vo: Makefile.coq %.v
#	$(MAKE_COQ) $*.vo

%.vo: %.v
	@echo coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<
	@coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<

include deps.mk

deps.mk:
	$(ISADK_DIR)/coqdep.sh $(SESSION) $(V_FILES) > $@
