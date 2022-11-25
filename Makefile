ISABELLE ?= isabelle

THY_NAME ?= HOL.Groups #Complex_Main

THY_FILE := $(shell echo $(THY_NAME) | sed -e 's/\./_/g')

SCALA_SRC := $(wildcard src/*.scala)

default: dk lp

dk: $(THY_FILE).dko

lp: $(THY_FILE).lpo

component:
	$(ISABELLE) components -u .

scala:
	$(ISABELLE) scala_build

ROOT: $(SCALA_SRC)
	$(ISABELLE) dedukti_root HOL

build: ROOT
	$(ISABELLE) build -b Dedukti_$(THY_NAME)

$(THY_FILE).lp: $(SCALA_SRC)
	$(ISABELLE) dedukti_session -l -v HOL $(THY_NAME)

$(THY_FILE).lpo: $(THY_FILE).lp
	lambdapi check $(THY_FILE).lp

$(THY_FILE).dk: $(SCALA_SRC)
	$(ISABELLE) dedukti_session -v HOL $(THY_NAME)

deps.mk: $(THY_FILE).dk
	dk dep *.dk > deps.mk

$(THY_FILE).dko: $(THY_FILE).dk deps.mk
	make -f dedukti.mk

clean:
	rm -f HOL*.dk HOL*.lp Pure.dk Pure.lp Tools*.dk Tools*.lp
