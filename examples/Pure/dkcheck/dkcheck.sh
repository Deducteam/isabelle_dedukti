#!/bin/sh
for f in Pure.dk
do
  dk check -e --eta $f -I ../../../logic || exit 1
done
