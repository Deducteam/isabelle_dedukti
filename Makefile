SRC := $(wildcard src/*.scala)

default: test-lp

component:
	isabelle components -u .

build:
	isabelle scala_build

lp: $(SRC)
	isabelle dedukti_generate -O main.lp -b -v -r HOL.Groups HOL
	lambdapi check HOL_Groups.lp

dk: $(SRC)
	isabelle dedukti_generate -O main.dk -b -v -r HOL.Groups HOL
	make -f dedukti.mk

clean:
	rm -f HOL*.dk HOL*.lp Pure.dk Pure.lp Tools*.dk Tools*.lp
