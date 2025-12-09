CHK ?= dk check -e --eta

.SUFFIXES:

SRC := $(wildcard *.dk)
OBJ := $(SRC:%=%o)

default: $(OBJ)

%.dko: %.dk
	$(CHK) $<

clean:
	rm -f $(wildcard *.dko)

include deps.mk
