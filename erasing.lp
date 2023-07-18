/* dk/lp symbols (on the right) the declarations of which are removed
and whose uses are replaced by the given Coq expressions (on the left) */

/****************************************************************************/
// STTfa

builtin "Type'" ≔ STTfa.Set;
builtin "Prop" ≔ STTfa.prop;
builtin "arr" ≔ STTfa.arr;
builtin "imp" ≔ STTfa.imp;
builtin "all" ≔ STTfa.all;

/****************************************************************************/
// Pure

builtin "" ≔ Pure.itself;
builtin "Isabelle.dummy" ≔ Pure.dummy;
builtin "@eq" ≔ Pure.eq;
builtin "" ≔ Pure.prop_const;
builtin "type" ≔ Pure.type;
builtin "Isabelle.dummy_pattern" ≔ Pure.dummy_pattern;
//Appt
//AppP
//Abst
//AbsP
//Hyp
//Oracle
//PClass
//MinProof
//term
//sort_constraint
//conjunction
builtin "@eq_refl Prop" ≔ Pure.prop_def;
//term_def
//sort_constraint_def
//conjunction_def
builtin "@eq_refl" ≔ Pure.reflexive;
builtin "@eq_sym" ≔ Pure.symmetric;
builtin "@eq_trans" ≔ Pure.transitive;
//equal_intr
//equal_elim
//abstract_rule
builtin "Isabelle.combination" ≔ Pure.combination;

builtin "Pure.prop_def_thm" ≔ Pure.prop_def_thm; // unused

/****************************************************************************/
// HOL_HOL

//type_class
//default
//equal
builtin "Prop" ≔ HOL_HOL.bool;
//type_class_const
builtin "Isabelle.Trueprop" ≔ HOL_HOL.Trueprop;
builtin "imp" ≔ HOL_HOL.implies; // undefined in Isabelle
builtin "@eq" ≔ HOL_HOL.eq_const;
//The
builtin "True" ≔ HOL_HOL.True;
builtin "@all" ≔ HOL_HOL.All;
builtin "@ex" ≔ HOL_HOL.Ex;
builtin "False" ≔ HOL_HOL.False;
builtin "not" ≔ HOL_HOL.Not;
builtin "and" ≔ HOL_HOL.conj;
builtin "or" ≔ HOL_HOL.disj;
//Uniq
//Ex1
//If
//Let
builtin "Isabelle.undefined" ≔ HOL_HOL.undefined;
//default_class_default
//default_class
builtin "imp" ≔ HOL_HOL.simp_implies;
builtin "all" ≔ HOL_HOL.induct_forall;
builtin "imp" ≔ HOL_HOL.induct_implies;
builtin "@eq" ≔ HOL_HOL.induct_equal;
builtin "and" ≔ HOL_HOL.induct_conj;
builtin "True" ≔ HOL_HOL.induct_true;
builtin "False" ≔ HOL_HOL.induct_false;
//NO_MATCH
//ASSUMPTION
//class_equal
//equal_class_equal
//equal_itself_inst_equal_itself
//fun_arity
//itself_arity
//arity_type_bool
//True_def_raw
//All_def_raw
//Ex_def_raw
//False_def_raw
//not_def_raw
//and_def_raw
//or_def_raw
//Uniq_def_raw
//Ex1_def_raw
//refl
//subst
//ext
//the_eq_trivial
//impI
//mp
//True_or_False
//If_def_raw
//Let_def_raw
//default_class_def
//eq_reflection
//simp_implies_def_raw
//induct_forall_def_raw
//induct_implies_def_raw
//induct_equal_def_raw
//induct_conj_def_raw
//induct_true_def_raw
//induct_false_def_raw
//NO_MATCH_def_raw
//ASSUMPTION_def_raw
//class_equal_def
//equal_class_def
//equal_itself_inst_equal_itself_def
//equal_itself_def_raw
