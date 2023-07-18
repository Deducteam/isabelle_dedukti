#!/bin/sh
for f in STTfa.dk Pure.dk
do
  dk check -e --eta $f || exit 1
done
