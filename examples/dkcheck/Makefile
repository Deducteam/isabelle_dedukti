ISADK_DIR ?= ../..

.SUFFIXES:

DK_FILES := $(wildcard *.dk)
V_FILES := $(DK_FILES:%.dk=%.v)

.PHONY: default
default: vo

MAKE_COQ := $(MAKE) -f coq.mk

.PHONY: vo
vo: coq.mk $(wildcard *.v) #$(V_FILES)
	$(MAKE_COQ)

coq.mk: _CoqProject
	coq_makefile -f $< -o $@
	# do not recompute dependencies each time a coq file is changed:
	sed -i -e 's/^$$(VDFILE): _CoqProject $$(VFILES)/$$(VDFILE):/' $@

_CoqProject: $(V_FILES)
	touch $@

#VO_FILES := $(V_FILES:%.v=%.vo)
#vo: $(VO_FILES)

#%.vo: coq.mk %.v
#	$(MAKE_COQ) $*.vo

#%.vo: %.v
#	@echo coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<
#	@coqc `awk '/^-Q /{printf" %s",$$0}' _CoqProject` $<

#include deps.mk

#deps.mk:
#	$(ISADK_DIR)/coqdeps.sh > $@

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-cache

.PHONY: rm-vo
rm-vo:
	find . -maxdepth 1 -name '*.vo*' -delete

.PHONY: rm-glob
rm-glob:
	find . -maxdepth 1 -name '*.glob' -delete

.PHONY: rm-aux
rm-aux:
	find . -maxdepth 1 -name '.*.aux' -delete

.PHONY: rm-cache
rm-cache:
	rm -f .lia.cache .nia.cache

.PHONY: rm-coq-mk
rm-coq-mk:
	-rm -f coq.mk coq.mk.conf
#	-rm -f deps.mk

.PHONY: v
v: $(V_FILES)

LAMBDAPI ?= lambdapi

#SESSION := $(shell awk -f $(ISADK_DIR)/session.awk _CoqProject)

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --renaming $(ISADK_DIR)/renaming.lp --requiring Isabelle.Isabelle.v --no-implicits $*.dk > $*.v

.PHONY: clean-v
clean-v: rm-v clean-vo rm-coq-mk

.PHONY: rm-v
rm-v:
	find . -maxdepth 1 -name '*.v' -a ! -name Isabelle.v -delete

.PHONY: rm-dk
rm-dk:
	find . -maxdepth 1 -name '*.dk' -a ! -name STTfa.dk -delete

.PHONY: rm-sh
rm-sh:
	find . -maxdepth 1 -name '*.sh' -a ! -name dkcheck_STTfa.sh -delete

.PHONY: rm-dko
rm-dko:
	find . -maxdepth 1 -name '*.dko' -delete

.PHONY: rm-lp
rm-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name STTfa.lp -delete

.PHONY: rm-lpo
rm-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: clean-dk
clean-dk: rm-dk rm-dko clean-v rm-sh

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo clean-v

.PHONY: clean-all
clean-all: clean-dk clean-lp
