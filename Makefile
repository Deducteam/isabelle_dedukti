SRC := $(wildcard src/*.scala)

default: dk dko

component:
	isabelle components -u .

build:
	isabelle scala_build

THY := HOL.Groups
FILE := HOL_Groups

#THY := Complex_Main
#FILE := $(THY)

lp: $(SRC)
	isabelle dedukti_generate -O main.lp -b -v -r $(THY) HOL

lpo: $(FILE).lp
	lambdapi check $<

dk: $(SRC)
	isabelle dedukti_generate -O main.dk -b -v -r $(THY) HOL

dko: $(FILE).dk
	dk dep *.dk > deps.mk
	make -f dedukti.mk

clean:
	rm -f HOL*.dk HOL*.lp Pure.dk Pure.lp Tools*.dk Tools*.lp
