#!/bin/sh

COQC='coqc -R . Isabelle'

f=Isabelle
if test \( ! -f $f.vo \) -o \( $f.v -nt $f.vo \)
then
    echo coqc Isabelle.v
    $COQC Isabelle.v
fi

for f in STTfa Pure Tools_Code_Generator HOL_HOL HOL_Argo HOL_SAT HOL_Ctr_Sugar HOL_Orderings HOL_Groups HOL_Lattices HOL_Boolean_Algebras HOL_Set HOL_Fun HOL_Complete_Lattices HOL_Inductive HOL_Typedef HOL_Product_Type HOL_Complete_Partial_Order HOL_Sum_Type HOL_Rings HOL_Nat HOL_Fields HOL_Finite_Set HOL_Relation HOL_Transitive_Closure HOL_Wellfounded HOL_Fun_Def_Base HOL_Hilbert_Choice HOL_Wfrec HOL_Order_Relation HOL_BNF_Wellorder_Relation HOL_BNF_Wellorder_Embedding HOL_BNF_Wellorder_Constructions HOL_Zorn HOL_BNF_Cardinal_Order_Relation HOL_BNF_Cardinal_Arithmetic HOL_BNF_Def HOL_BNF_Composition HOL_Basic_BNFs HOL_BNF_Fixpoint_Base HOL_BNF_Least_Fixpoint HOL_Basic_BNF_LFPs HOL_Equiv_Relations HOL_Meson HOL_ATP HOL_Metis HOL_Transfer HOL_Lifting HOL_Option HOL_Extraction HOL_Partial_Function HOL_Fun_Def HOL_Quotient HOL_Num HOL_Power HOL_Groups_Big HOL_Int HOL_Lattices_Big HOL_Euclidean_Division HOL_Parity HOL_Divides HOL_Numeral_Simprocs HOL_SMT HOL_Semiring_Normalization HOL_Groebner_Basis HOL_Set_Interval HOL_Conditionally_Complete_Lattices HOL_Presburger HOL_Sledgehammer HOL_Lifting_Set HOL_Filter HOL_List HOL_Groups_List HOL_Bit_Operations HOL_Code_Numeral HOL_Factorial HOL_Binomial HOL_GCD HOL_Map HOL_Enum HOL_String HOL_BNF_Greatest_Fixpoint HOL_Predicate HOL_Lazy_Sequence HOL_Limited_Sequence HOL_Typerep HOL_Code_Evaluation HOL_Random HOL_Quickcheck_Random HOL_Quickcheck_Exhaustive HOL_Quickcheck_Narrowing HOL_Random_Pred HOL_Random_Sequence HOL_Predicate_Compile HOL_Mirabelle Main HOL_Archimedean_Field HOL_Rat HOL_Real HOL_Hull HOL_Modules HOL_Vector_Spaces HOL_Topological_Spaces HOL_Real_Vector_Spaces HOL_Inequalities HOL_Limits HOL_Deriv HOL_NthRoot HOL_Series HOL_Transcendental HOL_Complex HOL_MacLaurin Complex_Main
do
    if test \( ! -f $f.v \) -o \( $f.dk -nt $f.v \)
    then
        echo lambdapi export -o stt_coq $f.dk
        lambdapi export -o stt_coq --encoding ../../encoding.lp --erasing ../../erasing.lp --renaming ../../renaming.lp --requiring Isabelle.v --no-implicits --use-notations $f.dk > $f.v || (rm -f $f.v; exit 1)
        sed -i -e 's/^Require /From Isabelle Require /' -e 's/Require STTfa./Require Import STTfa./' -e "s/$f.//g" $f.v
    fi
    if test \( ! -f $f.vo \) -o \( $f.v -nt $f.vo \)
    then
        echo coqc $f.v
        $COQC $f.v || exit 1
    fi
done
