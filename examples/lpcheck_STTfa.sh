#!/bin/sh
D=`dirname "$0"`
(cd $D; lambdapi check -c -w -v0 STTfa.lp) || exit 1
