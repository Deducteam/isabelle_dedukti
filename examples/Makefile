.SUFFIXES:

.PHONY: default help
default help:
	@echo usage: make [-j JOBS] [target] [VAR=VAL] ...
	@echo targets: build, dk, dko, v, dep, vo, session, sessions, clean-[target,all]
	@echo variables: ISADK_DIR, ISADK_OPT, ISADB_DIR, ROOT_DIR, SESSION, SESSIONS, OUT_DIR

TIME = /usr/bin/time -f %e

############# generation of Coq files ##############

DK_FILES := $(wildcard *.dk)

.PHONY: v
v: $(DK_FILES:%.dk=%.v)

LAMBDAPI = lambdapi

%.v: %.dk
	$(LAMBDAPI) export -o stt_coq --encoding $(ISADK_DIR)/encoding.lp --erasing $(ISADK_DIR)/erasing.lp --renaming $(ISADK_DIR)/renaming.lp --requiring Isabelle.Isabelle.v --no-implicits $*.dk > $*.v

.PHONY: clean-v
clean-v: rm-v clean-vo clean-dep

.PHONY: rm-v
rm-v:
	find $(OUT_DIR) -maxdepth 1 -name '*.v' -a ! -name Isabelle.v -delete

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
	-rm -f $(OUT_DIR)/$(COQ_MAKEFILE) $(OUT_DIR)/$(COQ_MAKEFILE).conf $(OUT_DIR)/$(VDFILE)

############# verification of Coq files ##############

.PHONY: vo
vo:
	+$(MAKE_COQ)

.PHONY: clean-vo
clean-vo: rm-vo rm-glob rm-aux rm-caches

.PHONY: rm-vo
rm-vo:
	find $(OUT_DIR) -maxdepth 1 -name '*.vo*' -delete

.PHONY: rm-glob
rm-glob:
	find $(OUT_DIR) -maxdepth 1 -name '*.glob' -delete

.PHONY: rm-aux
rm-aux:
	find $(OUT_DIR) -maxdepth 1 -name '.*.aux' -delete

.PHONY: rm-caches
rm-caches:
	rm -f $(OUT_DIR)/.lia.cache $(OUT_DIR)/.nia.cache

############# generation of Isabelle proofs ##############

ISADB_DIR =
ROOT_DIR = .
OUT_DIR = ./output
SESSION = HOL_Nat_wp
MOD_NAME_SESSION = session_$(subst .,_,$(subst -,_,$(SESSION)))

.PHONY: build
build: $(ISADB_DIR)/$(SESSION).db

$(ISADB_DIR)/%.db: $(ROOT_DIR)/ROOT $(SESSION)
	isabelle build -b -d$(ROOT_DIR) $*

$(SESSION):
	mkdir -p $@

clean-build:
	rm -f $(ISADB_DIR)/$(SESSION).db

############# generation of Dedukti files ##############

.PHONY: dk
dk: $(OUT_DIR)/$(MOD_NAME_SESSION).dk

$(OUT_DIR)/$(MOD_NAME_SESSION).dk:
	isabelle dk_translate -k -d$(ROOT_DIR) -D$(OUT_DIR) $(ISADK_OPT) -r $(SESSION)

.PHONY: clean-dk
clean-dk: rm-dk rm-sh rm-dko clean-v

.PHONY: rm-dk
rm-dk:
	find $(OUT_DIR) -maxdepth 1 -name '*.dk' -a ! -name STTfa.dk -delete

############# verification of Dedukti files ##############

ifeq ($(INCLUDE_DKO_MK),1)
include dkcheck_$(SESSION).mk
endif

.PHONY:dko
dko: $(OUT_DIR)/$(MOD_NAME_SESSION).dko
ifneq ($(INCLUDE_DKO_MK),1)
	$(MAKE) INCLUDE_DKO_MK=1 $@
endif

%.dko: %.dk
	dk check -e --eta $<

.PHONY: clean-dko
clean-dko: rm-dko

.PHONY: rm-dko
rm-dko:
	find $(OUT_DIR) -maxdepth 1 -name '*.dko' -delete

############# generation of Lambdapi files ##############

.PHONY: lp
lp: $(OUT_DIR)/$(MOD_NAME_SESSION).lp

$(OUT_DIR)/$(MOD_NAME_SESSION).lp:
	isabelle dk_translate -d$(ROOT_DIR) -D$(OUT_DIR) $(ISADK_OPT) -r $(SESSION)

.PHONY: clean-lp
clean-lp: rm-lp rm-lpo clean-v

.PHONY: rm-lp
rm-lp:
	find $(OUT_DIR) -maxdepth 1 -name '*.lp' -a ! -name STTfa.lp -delete

############# verification of Lambdapi files ##############

ifeq ($(INCLUDE_LPO_MK),1)
include lpcheck_$(SESSION).mk
endif

.PHONY:lpo
lpo: $(OUT_DIR)/$(MOD_NAME_SESSION).lpo
ifneq ($(INCLUDE_LPO_MK),1)
	$(MAKE) INCLUDE_LPO_MK=1 $@
endif

%.lpo: %.lp
	lambdapi check -c -w -v0 $<

.PHONY: clean-lpo
clean-lpo: rm-lpo

.PHONY: rm-lpo
rm-lpo:
	find $(OUT_DIR) -maxdepth 1 -name '*.lpo' -delete

############# testing ##############

.PHONY: session
session:
	@echo $(MAKE) build SESSION=$(SESSION)
	$(TIME) $(MAKE) build > /dev/null
	@echo $(MAKE) dk SESSION=$(SESSION)
	$(TIME) $(MAKE) dk > /dev/null
	@echo $(MAKE) dko SESSION=$(SESSION)
	$(TIME) $(MAKE) dko > /dev/null
	@echo $(MAKE) v SESSION=$(SESSION)
	$(TIME) $(MAKE) v > /dev/null
	@echo $(MAKE) dep SESSION=$(SESSION)
	$(TIME) $(MAKE) dep > /dev/null
	@echo $(MAKE) vo SESSION=$(SESSION)
	$(TIME) $(MAKE) vo > /dev/null

.PHONY: clean-session
clean-session: clean-dk clean-lp clean-build

.PHONY: sessions
sessions:
	for SESSION in $(SESSIONS); do $(MAKE) SESSION=$$SESSION; done

.PHONY: clean-sessions
clean-sessions:
	for SESSION in $(SESSIONS); do $(MAKE) SESSION=$$SESSION clean-session; done
