.SUFFIXES:

.PHONY: default
default:
	@echo targets: build, dk, dko, v, dep, vo, clean-[target,all]
	@echo variables: ISADB_DIR, ROOT_DIR, SESSION

############# generation of Coq files ##############

DK_FILES := $(wildcard *.dk)

.PHONY: v
v: $(DK_FILES:%.dk=%.v)

LAMBDAPI = lambdapi

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --renaming $(ISADK_DIR)/renaming.lp --requiring Isabelle.Isabelle.v --no-implicits $*.dk > $*.v

.PHONY: clean-v
clean-v: rm-v clean-vo #clean-dep

.PHONY: rm-v
rm-v:
	find . -maxdepth 1 -name '*.v' -a ! -name Isabelle.v -delete

############# dependencies of Coq files ##############

COQ_MAKEFILE := coq.mk
MAKE_COQ := $(MAKE) -f $(COQ_MAKEFILE)
VDFILE := .$(COQ_MAKEFILE).d

.PHONY: dep
dep:
	coq_makefile -f _CoqProject -o $(COQ_MAKEFILE)
	# compute dependencies
	+$(MAKE_COQ) $(VDFILE)
	# do not recompute dependencies
	sed -i -e 's/^$$(VDFILE): _CoqProject $$(VFILES)/$$(VDFILE):/' $(COQ_MAKEFILE)

.PHONY: clean-dep
clean-dep:
	-rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf $(VDFILE)

############# verification of Coq files ##############

.PHONY: vo
vo:
	+$(MAKE_COQ)

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-caches

.PHONY: rm-vo
rm-vo:
	find . -maxdepth 1 -name '*.vo*' -delete

.PHONY: rm-glob
rm-glob:
	find . -maxdepth 1 -name '*.glob' -delete

.PHONY: rm-aux
rm-aux:
	find . -maxdepth 1 -name '.*.aux' -delete

.PHONY: rm-caches
rm-caches:
	rm -f .lia.cache .nia.cache

############# generation of Isabelle proofs ##############

ISADB_DIR = ~/.isabelle/Isabelle2023/heaps/polyml-5.9_x86_64_32-linux/log
ROOT_DIR = .
SESSION = HOL_Nat_wp

.PHONY: build
build: $(ISADB_DIR)/$(SESSION).db

$(ISADB_DIR)/%.db: $(ROOT_DIR)/ROOT
	isabelle build -b -d$(ROOT_DIR) $*

clean-build:
	rm -f $(ISADB_DIR)/$(SESSION).db $(ISADB_DIR)/$(SESSION).gz

############# generation of Dedukti files ##############

.PHONY: dk
dk: session_$(SESSION).dk

session_%.dk:
	isabelle dedukti_session -d$(ROOT_DIR) -r $*

.PHONY: clean-dk
clean-dk: rm-dk rm-sh rm-dko clean-v

.PHONY: rm-dk
rm-dk:
	find . -maxdepth 1 -name '*.dk' -a ! -name STTfa.dk -delete

.PHONY: rm-sh
rm-sh:
	find . -maxdepth 1 -name '*.sh' -a ! -name dkcheck_STTfa.sh -delete

############# verification of Dedukti files ##############

.PHONY:dko
dko: session_$(SESSION).dko

session_%.dko: session_%.dk
	bash dkcheck_session_$*.sh

.PHONY: clean-dko
clean-dko: rm-dko

.PHONY: rm-dko
rm-dko:
	find . -maxdepth 1 -name '*.dko' -delete

############# generation of Lambdapi files ##############

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo

.PHONY: rm-lp
rm-lp:
	find . -maxdepth 1 -name '*.lp' -a ! -name STTfa.lp -delete

############# verification of Lambdapi files ##############

.PHONY: clean-lpo
clean-lpo: rm-lpo

.PHONY: rm-lpo
rm-lpo:
	find . -maxdepth 1 -name '*.lpo' -delete

.PHONY: clean-all
clean-all: clean-dk clean-lp
