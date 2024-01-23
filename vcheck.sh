#!/bin/sh

make="make -f $ISADK_DIR/Makefile $*"

$make -C $ISADK_DIR/coq Isabelle.vo

for d in `awk '/^-Q /{if($2!="."){print $2}}' _CoqProject`
do
    $make -C $d
done

$make clean-v
$make v
rm -f deps.mk
$make vo
