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
builtin "dummy" ≔ Pure.dummy;
builtin "@eq" ≔ Pure.eq;
builtin "" ≔ Pure.prop_const;
builtin "el" ≔ Pure.type;
builtin "el" ≔ Pure.dummy_pattern;
builtin "proof" ≔ proof; // unused
builtin "Appt" ≔ Appt; // unused
builtin "AppP" ≔ AppP; // unused
builtin "Abst" ≔ Abst; // unused
builtin "AbsP" ≔ AbsP; // unused
builtin "Hyp" ≔ Hyp; // unused
builtin "Oracle" ≔ Oracle; // unused
builtin "PClass" ≔ PClass; // unused
builtin "MinProof" ≔ MinProof; // unused
builtin "term" ≔ Pure.term;
builtin "sort_constraint" ≔ Pure.sort_constraint;
builtin "conjunction" ≔ Pure.conjunction;
builtin "term_def" ≔ Pure.term_def;
builtin "sort_constraint_def" ≔ Pure.sort_constraint_def;
builtin "conjunction_def" ≔ Pure.conjunction_def;
builtin "@eq_refl Prop" ≔ Pure.prop_def;
builtin "@eq_refl" ≔ Pure.reflexive;
builtin "@eq_sym" ≔ Pure.symmetric;
builtin "@eq_trans" ≔ Pure.transitive;
builtin "equal_intr" ≔ Pure.equal_intr;
builtin "equal_elim" ≔ Pure.equal_elim;
builtin "abstract_rule" ≔ Pure.abstract_rule;
builtin "combination" ≔ Pure.combination;
builtin "Pure.prop_def_thm" ≔ Pure.prop_def_thm; // unused

/****************************************************************************/
// Tools_Code_generator

builtin "holds" ≔ Tools_Code_Generator.holds;
builtin "holds_def_raw" ≔ Tools_Code_Generator.holds_def_raw;

/****************************************************************************/
// HOL_HOL

//type_class
//default
//equal
builtin "Prop" ≔ HOL_HOL.bool;
//type_class_const
builtin "Trueprop" ≔ HOL_HOL.Trueprop; // cannot be replaced by ""
builtin "imp" ≔ HOL_HOL.implies;
builtin "@eq" ≔ HOL_HOL.eq_const;
builtin "The" ≔ HOL_HOL.The;
builtin "True" ≔ HOL_HOL.True;
builtin "@all" ≔ HOL_HOL.All;
builtin "@ex" ≔ HOL_HOL.Ex;
builtin "False" ≔ HOL_HOL.False;
builtin "not" ≔ HOL_HOL.Not;
builtin "and" ≔ HOL_HOL.conj;
builtin "or" ≔ HOL_HOL.disj;
builtin "Uniq" ≔ HOL_HOL.Uniq;
builtin "Ex1" ≔ HOL_HOL.Ex1;
builtin "If" ≔ HOL_HOL.If;
builtin "Let" ≔ HOL_HOL.Let;
builtin "el" ≔ HOL_HOL.undefined;
builtin "default_class_default" ≔ HOL_HOL.default_class_default;
//default_class
builtin "imp" ≔ HOL_HOL.simp_implies;
builtin "all" ≔ HOL_HOL.induct_forall;
builtin "imp" ≔ HOL_HOL.induct_implies;
builtin "@eq" ≔ HOL_HOL.induct_equal;
builtin "and" ≔ HOL_HOL.induct_conj;
builtin "True" ≔ HOL_HOL.induct_true;
builtin "False" ≔ HOL_HOL.induct_false;
builtin "NO_MATCH" ≔ HOL_HOL.NO_MATCH;
builtin "ASSUMPTION" ≔ HOL_HOL.ASSUMPTION;
builtin "class_equal" ≔ HOL_HOL.class_equal;
//equal_class_equal
//equal_itself_inst_equal_itself
//fun_arity
//itself_arity
//arity_type_bool
builtin "True_def_raw" ≔ HOL_HOL.True_def_raw;
builtin "All_def_raw" ≔ HOL_HOL.All_def_raw;
builtin "Ex_def_raw" ≔ HOL_HOL.Ex_def_raw;
builtin "False_def_raw" ≔ HOL_HOL.False_def_raw;
builtin "not_def_raw" ≔ HOL_HOL.not_def_raw;
builtin "and_def_raw" ≔ HOL_HOL.and_def_raw;
builtin "or_def_raw" ≔ HOL_HOL.or_def_raw;
builtin "Uniq_def_raw" ≔ HOL_HOL.Uniq_def_raw;
builtin "Ex1_def_raw" ≔ HOL_HOL.Ex1_def_raw;
//refl
//subst
//ext
//the_eq_trivial
builtin "impI" ≔ HOL_HOL.impI;
builtin "mp" ≔ HOL_HOL.mp;
builtin "True_or_False" ≔ HOL_HOL.True_or_False;
builtin "If_def_raw" ≔ HOL_HOL.If_def_raw;
builtin "Let_def_raw" ≔ HOL_HOL.Let_def_raw;
//default_class_def
//eq_reflection
builtin "simp_implies_def_raw" ≔ HOL_HOL.simp_implies_def_raw;
builtin "induct_forall_def_raw" ≔ HOL_HOL.induct_forall_def_raw;
builtin "induct_implies_def_raw" ≔ HOL_HOL.induct_implies_def_raw;
builtin "induct_equal_def_raw" ≔ HOL_HOL.induct_equal_def_raw;
builtin "induct_conj_def_raw" ≔ HOL_HOL.induct_conj_def_raw;
builtin "induct_true_def_raw" ≔ HOL_HOL.induct_true_def_raw;
builtin "induct_false_def_raw" ≔ HOL_HOL.induct_false_def_raw;
builtin "NO_MATCH_def_raw" ≔ HOL_HOL.NO_MATCH_def_raw;
builtin "ASSUMPTION_def_raw" ≔ HOL_HOL.ASSUMPTION_def_raw;
builtin "class_equal_def" ≔ HOL_HOL.class_equal_def;
//equal_class_def
//equal_itself_inst_equal_itself_def
//equal_itself_def_raw
