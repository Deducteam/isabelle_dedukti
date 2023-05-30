#!/bin/sh

set -x
mkdir kocheck
for f in $*
do
    sed -e 's/#REQUIRE.*//' -e "s/${f%.dk}\.//g" $f > kocheck/$f
done
