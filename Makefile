ISABELLE ?= isabelle

THY_NAME ?= HOL.Groups #Complex_Main

THY_FILE := $(shell echo $(THY_NAME) | sed -e 's/\./_/g')

SCALA_SRC := $(wildcard src/*.scala)

default: dko lpo

dko: $(THY_FILE).dko

lpo: $(THY_FILE).lpo

component:
	$(ISABELLE) components -u .

scala:
	$(ISABELLE) scala_build

force_root ROOT dkcheck.sh kocheck.sh: $(SCALA_SRC)
	$(ISABELLE) dedukti_root HOL $(THY_NAME)

build: ROOT
	$(ISABELLE) build -b Dedukti_$(THY_NAME)

$(THY_FILE).lp: $(SCALA_SRC)
	$(ISABELLE) dedukti_session -l -v HOL $(THY_NAME)

$(THY_FILE).lpo: STTfa.lp $(THY_FILE).lp
	lambdapi check $(THY_FILE).lp

$(THY_FILE).dk: $(SCALA_SRC)
	$(ISABELLE) dedukti_session -v HOL $(THY_NAME)

deps.mk: $(THY_FILE).dk
	dk dep *.dk > deps.mk

$(THY_FILE).dko: STTfa.dk $(THY_FILE).dk #deps.mk
	#make -f dedukti.mk
	bash ./dkcheck.sh

clean:
	-rm -f ROOT dkcheck.sh kocheck.sh deps.mk
	-rm -f Pure.dk Tools*.dk HOL*.dk *.dko
	-rm -f Pure.lp Tools*.lp HOL*.lp *.lpo
