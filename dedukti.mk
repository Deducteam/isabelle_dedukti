CHK ?= dk check -e --eta

.SUFFIXES:

SRC := $(wildcard *.dk)
OBJ := $(SRC:%=%o)

default: $(OBJ)

include deps.mk

%.dko: %.dk
	$(CHK) $<

clean:
	rm -f $(wildcard *.dko)
