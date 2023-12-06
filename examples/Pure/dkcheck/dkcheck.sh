#!/bin/sh
for f in STTfa.dk Pure.dk Pure_session.dk
do
  dk check -e --eta $f || exit 1
done
