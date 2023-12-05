#!/bin/sh

session=`awk '/^-Q /{session=$3;next}/.v/{printf"%s",session;exit}' _CoqProject`
vfiles=`awk '/^-Q /{next}/.v/{printf" %s",$1;next}' _CoqProject`
tmp=/tmp/coqdep.awk

for f in $vfiles
do
    echo -n "${f%.v}.vo:"
    echo "BEGIN{FS=\"[ .]\"}/^From $session /{if(\$4==\"Import\"){printf\" %s.vo\",\$5}else{printf\" %s.vo\",\$4};next}/^Axiom /{nextfile}/^Lemma /{nextfile}" > $tmp
    awk -f $tmp $f
    #awk 'BEGIN{FS="[ .]"}/^From /{if($4=="Import"){printf" %s.vo",$5}else{printf" %s.vo",$4};next}/^Axiom /{nextfile}/^Lemma /{nextfile}' $f
    echo
done
