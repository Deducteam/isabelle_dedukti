/* dk/lp symbols (on the right) the declarations of which are removed
and whose uses are replaced by the given Coq expressions (on the left) */

/****************************************************************************/
/* STTfa */

builtin "Type'" ≔ STTfa.Set;
builtin "Prop" ≔ STTfa.prop;
builtin "arr" ≔ STTfa.arr;
builtin "imp" ≔ STTfa.imp;
builtin "all" ≔ STTfa.all;

/****************************************************************************/
/* Pure */

builtin "@eq" ≔ Pure.eq;

builtin "dummy" ≔ Pure.dummy;
builtin "el" ≔ Pure.dummy_pattern;

builtin "HOL2DK_proof" ≔ proof; // unused
builtin "HOL2DK_Appt" ≔ Appt; // unused
builtin "HOL2DK_AppP" ≔ AppP; // unused
builtin "HOL2DK_Abst" ≔ Abst; // unused
builtin "HOL2DK_AbsP" ≔ AbsP; // unused
builtin "HOL2DK_Hyp" ≔ Hyp; // unused
builtin "HOL2DK_Oracle" ≔ Oracle; // unused
builtin "HOL2DK_PClass" ≔ PClass; // unused
builtin "HOL2DK_MinProof" ≔ MinProof; // unused

builtin "itself" ≔ Pure.itself;
builtin "unit" ≔ Pure.type;

builtin "sort_constraint" ≔ Pure.sort_constraint;
builtin "sort_constraint_def" ≔ Pure.sort_constraint_def;

builtin "" ≔ Pure.prop_const; // is defined as the identity

builtin "@eq_refl" ≔ Pure.reflexive;
builtin "@eq_sym" ≔ Pure.symmetric;
builtin "@eq_trans" ≔ Pure.transitive;
builtin "equal_intr" ≔ Pure.equal_intr;
builtin "equal_elim" ≔ Pure.equal_elim;

builtin "abstract_rule" ≔ Pure.abstract_rule;
builtin "combination" ≔ Pure.combination;

/* simplification */

builtin "and" ≔ Pure.conjunction;
builtin "conjunction_def" ≔ Pure.conjunction_def;

/****************************************************************************/
/* HOL_HOL */

builtin "el" ≔ HOL_HOL.undefined;
builtin "Prop" ≔ HOL_HOL.bool;
builtin "Trueprop" ≔ HOL_HOL.Trueprop; // cannot be replaced by ""
builtin "imp" ≔ HOL_HOL.implies;
builtin "@eq" ≔ HOL_HOL.eq_const;
builtin "@ε" ≔ HOL_HOL.The;
builtin "impI" ≔ HOL_HOL.impI;
builtin "mp" ≔ HOL_HOL.mp;
builtin "True_or_False" ≔ HOL_HOL.True_or_False;
builtin "eq_reflection" ≔ HOL_HOL.eq_reflection;

/* connectives */

builtin "True" ≔ HOL_HOL.True;
builtin "True_def_raw" ≔ HOL_HOL.True_def_raw;

builtin "False" ≔ HOL_HOL.False;
builtin "False_def_raw" ≔ HOL_HOL.False_def_raw;

builtin "@all" ≔ HOL_HOL.All;
builtin "All_def_raw" ≔ HOL_HOL.All_def_raw;

builtin "@ex" ≔ HOL_HOL.Ex;
builtin "Ex_def_raw" ≔ HOL_HOL.Ex_def_raw;

builtin "not" ≔ HOL_HOL.Not;
builtin "not_def_raw" ≔ HOL_HOL.not_def_raw;

builtin "and" ≔ HOL_HOL.conj;
builtin "and_def_raw" ≔ HOL_HOL.and_def_raw;

builtin "or" ≔ HOL_HOL.disj;
builtin "or_def_raw" ≔ HOL_HOL.or_def_raw;

/* simplifications */

builtin "imp" ≔ HOL_HOL.simp_implies;
builtin "imp" ≔ HOL_HOL.induct_implies;
builtin "all" ≔ HOL_HOL.induct_forall;
builtin "@eq" ≔ HOL_HOL.induct_equal;
builtin "and" ≔ HOL_HOL.induct_conj;
builtin "True" ≔ HOL_HOL.induct_true;
builtin "False" ≔ HOL_HOL.induct_false;

/* class type (top class) */

builtin "type_class" ≔ HOL_HOL.type_class;

builtin "eq_reflection" ≔ HOL_HOL.eq_reflection;
builtin "refl" ≔ HOL_HOL.refl;
builtin "subst" ≔ HOL_HOL.subst;
builtin "ext" ≔ HOL_HOL.ext;
builtin "the_eq_trivial" ≔ HOL_HOL.the_eq_trivial;

//builtin "fun_arity" ≔ HOL_HOL.fun_arity;
//builtin "itself_arity" ≔ HOL_HOL.itself_arity;
