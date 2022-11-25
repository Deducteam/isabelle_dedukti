#!/bin/sh

set -x
for f in $*
do
    sed -e 's/#REQUIRE.*//' -e "s/${f%.dk}\.//g" $f > kocheck/$f
done
