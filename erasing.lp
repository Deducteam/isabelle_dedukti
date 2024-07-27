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

builtin "term" ≔ Pure.term;
builtin "term_def" ≔ Pure.term_def;

builtin "sort_constraint" ≔ Pure.sort_constraint;
builtin "sort_constraint_def" ≔ Pure.sort_constraint_def;

builtin "conjunction" ≔ Pure.conjunction;
builtin "conjunction_def" ≔ Pure.conjunction_def;

builtin "" ≔ Pure.prop_const; // is defined as the identity
builtin "@eq_refl Prop" ≔ Pure.prop_def;
builtin "HOL2DK_prop_def_thm" ≔ Pure.prop_def_thm; // unused

builtin "@eq_refl" ≔ Pure.reflexive;
builtin "@eq_sym" ≔ Pure.symmetric;
builtin "@eq_trans" ≔ Pure.transitive;
builtin "equal_intr" ≔ Pure.equal_intr;
builtin "equal_elim" ≔ Pure.equal_elim;

builtin "abstract_rule" ≔ Pure.abstract_rule;
builtin "combination" ≔ Pure.combination;

/****************************************************************************/
/* Tools_Code_generator */

builtin "holds" ≔ Tools_Code_Generator.holds;
builtin "holds_def_raw" ≔ Tools_Code_Generator.holds_def_raw;

/****************************************************************************/
/* HOL_HOL */

builtin "el" ≔ HOL_HOL.undefined;
builtin "Prop" ≔ HOL_HOL.bool;
builtin "Trueprop" ≔ HOL_HOL.Trueprop; // cannot be replaced by ""
builtin "imp" ≔ HOL_HOL.implies;
builtin "@eq" ≔ HOL_HOL.eq_const;
builtin "The" ≔ HOL_HOL.The;
builtin "impI" ≔ HOL_HOL.impI;
builtin "mp" ≔ HOL_HOL.mp;
builtin "True_or_False" ≔ HOL_HOL.True_or_False;
builtin "eq_reflection" ≔ HOL_HOL.eq_reflection;

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

builtin "Uniq" ≔ HOL_HOL.Uniq;
builtin "Uniq_def_raw" ≔ HOL_HOL.Uniq_def_raw;

builtin "Ex1" ≔ HOL_HOL.Ex1;
builtin "Ex1_def_raw" ≔ HOL_HOL.Ex1_def_raw;

builtin "If" ≔ HOL_HOL.If;
builtin "If_def_raw" ≔ HOL_HOL.If_def_raw;

builtin "Let" ≔ HOL_HOL.Let;
builtin "Let_def_raw" ≔ HOL_HOL.Let_def_raw;

builtin "True" ≔ HOL_HOL.induct_true;
builtin "induct_true_def_raw" ≔ HOL_HOL.induct_true_def_raw;

builtin "False" ≔ HOL_HOL.induct_false;
builtin "induct_false_def_raw" ≔ HOL_HOL.induct_false_def_raw;

builtin "NO_MATCH" ≔ HOL_HOL.NO_MATCH;
builtin "NO_MATCH_def_raw" ≔ HOL_HOL.NO_MATCH_def_raw;

builtin "ASSUMPTION" ≔ HOL_HOL.ASSUMPTION;
builtin "ASSUMPTION_def_raw" ≔ HOL_HOL.ASSUMPTION_def_raw;

builtin "imp" ≔ HOL_HOL.simp_implies;
builtin "simp_implies_def_raw" ≔ HOL_HOL.simp_implies_def_raw;

builtin "all" ≔ HOL_HOL.induct_forall;
builtin "induct_forall_def_raw" ≔ HOL_HOL.induct_forall_def_raw;

builtin "imp" ≔ HOL_HOL.induct_implies;
builtin "induct_implies_def_raw" ≔ HOL_HOL.induct_implies_def_raw;

builtin "@eq" ≔ HOL_HOL.induct_equal;
builtin "induct_equal_def_raw" ≔ HOL_HOL.induct_equal_def_raw;

builtin "and" ≔ HOL_HOL.induct_conj;
builtin "induct_conj_def_raw" ≔ HOL_HOL.induct_conj_def_raw;

/* class type (top class) */
builtin "type_class" ≔ HOL_HOL.type_class;
builtin "HOL2DK_type_class_const" ≔ type_class_const; // unused

builtin "eq_reflection" ≔ HOL_HOL.eq_reflection;
builtin "refl" ≔ HOL_HOL.refl;
builtin "subst" ≔ HOL_HOL.subst;
builtin "ext" ≔ HOL_HOL.ext;
builtin "the_eq_trivial" ≔ HOL_HOL.the_eq_trivial;

builtin "fun_arity" ≔ HOL_HOL.fun_arity;
builtin "itself_arity" ≔ HOL_HOL.itself_arity;

/* class default */
builtin "default_class_default" ≔ HOL_HOL.default_class_default;
builtin "default" ≔ HOL_HOL.default;
builtin "default_class_def" ≔ HOL_HOL.default_class_def;
builtin "HOL2DK_default_class" ≔ HOL_HOL.default_class; // unused

/* class equal */
builtin "class_equal" ≔ HOL_HOL.class_equal;
builtin "class_equal_def" ≔ HOL_HOL.class_equal_def;
builtin "equal_class_equal" ≔ HOL_HOL.equal_class_equal;
builtin "equal" ≔ HOL_HOL.equal;
builtin "equal_class_def" ≔ HOL_HOL.equal_class_def;
builtin "HOL2DK_equal_class" ≔ equal_class; // unused

//equal_itself_inst_equal_itself
//equal_itself_inst_equal_itself_def
//equal_itself_def_raw
