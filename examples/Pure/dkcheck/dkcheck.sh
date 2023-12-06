#!/bin/sh
for f in STTfa.dk Pure.dk session_Pure.dk
do
  dk check -e --eta $f || exit 1
done
