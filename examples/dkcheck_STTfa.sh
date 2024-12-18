#!/bin/sh
D=`dirname "$0"`
(cd $D; dk check -e --eta STTfa.dk) || exit 1
