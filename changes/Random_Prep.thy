(*  Title:      HOL/Quickcheck_Random.thy
    Author:     Florian Haftmann & Lukas Bulwahn, TU Muenchen
*)

section \<open>A simple counterexample generator performing random testing\<close>

theory Random_Prep
imports Random Code_Evaluation Enum
begin

(*setup \<open>Code_Target.add_derived_target ("Quickcheck", [(Code_Runtime.target, I)])\<close>*)

(*subsection \<open>Catching Match exceptions\<close>

axiomatization catch_match :: "'a => 'a => 'a"

code_printing
  constant catch_match \<rightharpoonup> (Quickcheck) "((_) handle Match => _)"

code_reserved Quickcheck Match*)

subsection \<open>The \<open>random\<close> class\<close>

class random = typerep +
  fixes random :: "natural \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed"


subsection \<open>Fundamental and numeric types\<close>

instantiation bool :: random
begin

context
  includes state_combinator_syntax
begin

definition
  "random i = Random.range 2 \<circ>\<rightarrow>
    (\<lambda>k. Pair (if k = 0 then Code_Evaluation.valtermify False else Code_Evaluation.valtermify True))"

instance ..

end

end

instantiation itself :: (typerep) random
begin

definition
  random_itself :: "natural \<Rightarrow> Random.seed \<Rightarrow> ('a itself \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
where "random_itself _ = Pair (Code_Evaluation.valtermify TYPE('a))"

instance ..

end

instantiation char :: random
begin

context
  includes state_combinator_syntax
begin

definition
  "random _ = Random.select (Enum.enum :: char list) \<circ>\<rightarrow> (\<lambda>c. Pair (c, \<lambda>u. Code_Evaluation.term_of c))"

instance ..

end

end

instantiation String.literal :: random
begin

definition
  "random _ = Pair (STR '''', \<lambda>u. Code_Evaluation.term_of (STR ''''))"

instance ..

end

instantiation nat :: random
begin

context
  includes state_combinator_syntax
begin

definition random_nat :: "natural \<Rightarrow> Random.seed
  \<Rightarrow> (nat \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_nat i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let n = nat_of_natural k
     in (n, \<lambda>_. Code_Evaluation.term_of n)))"

instance ..

end

end

instantiation int :: random
begin

context
  includes state_combinator_syntax
begin

definition
  "random i = Random.range (2 * i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let j = (if k \<ge> i then int (nat_of_natural (k - i)) else - (int (nat_of_natural (i - k))))
     in (j, \<lambda>_. Code_Evaluation.term_of j)))"

instance ..

end

end

instantiation natural :: random
begin

context
  includes state_combinator_syntax
begin

definition random_natural :: "natural \<Rightarrow> Random.seed
  \<Rightarrow> (natural \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_natural i = Random.range (i + 1) \<circ>\<rightarrow> (\<lambda>n. Pair (n, \<lambda>_. Code_Evaluation.term_of n))"

instance ..

end

end

instantiation integer :: random
begin

context
  includes state_combinator_syntax
begin

definition random_integer :: "natural \<Rightarrow> Random.seed
  \<Rightarrow> (integer \<times> (unit \<Rightarrow> Code_Evaluation.term)) \<times> Random.seed"
where
  "random_integer i = Random.range (2 * i + 1) \<circ>\<rightarrow> (\<lambda>k. Pair (
     let j = (if k \<ge> i then integer_of_natural (k - i) else - (integer_of_natural (i - k)))
      in (j, \<lambda>_. Code_Evaluation.term_of j)))"

instance ..

end

end


subsection \<open>Complex generators\<close>

text \<open>Towards \<^typ>\<open>'a \<Rightarrow> 'b\<close>\<close>

axiomatization random_fun_aux :: "typerep \<Rightarrow> typerep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
  \<Rightarrow> (Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> (Random.seed \<Rightarrow> Random.seed \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"

definition random_fun_lift :: "(Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a::term_of \<Rightarrow> 'b::typerep) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
where
  "random_fun_lift f =
    random_fun_aux TYPEREP('a) TYPEREP('b) (=) Code_Evaluation.term_of f Random.split_seed"

instantiation "fun" :: ("{equal, term_of}", random) random
begin

definition
  random_fun :: "natural \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"
  where "random i = random_fun_lift (random i)"

instance ..

end

(*text \<open>Towards type copies and datatypes\<close>

context
  includes state_combinator_syntax
begin

definition collapse :: "('a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a"
  where "collapse f = (f \<circ>\<rightarrow> id)"

end

definition beyond :: "natural \<Rightarrow> natural \<Rightarrow> natural"
  where "beyond k l = (if l > k then l else 0)"

lemma beyond_zero: "beyond k 0 = 0"
  by (simp add: beyond_def)

context
  includes term_syntax
begin

definition [code_unfold]:
  "valterm_emptyset = Code_Evaluation.valtermify ({} :: ('a :: typerep) set)"

definition [code_unfold]:
  "valtermify_insert x s = Code_Evaluation.valtermify insert {\<cdot>} (x :: ('a :: typerep * _)) {\<cdot>} s"

end

instantiation set :: (random) random
begin

context
  includes state_combinator_syntax
begin


fun random_aux_set
where
  "random_aux_set 0 j = collapse (Random.select_weight [(1, Pair valterm_emptyset)])"
| "random_aux_set (Code_Numeral.Suc i) j =
    collapse (Random.select_weight
      [(1, Pair valterm_emptyset),
       (Code_Numeral.Suc i,
        random j \<circ>\<rightarrow> (%x. random_aux_set i j \<circ>\<rightarrow> (%s. Pair (valtermify_insert x s))))])"


lemma [code]:
  "random_aux_set i j =
    collapse (Random.select_weight [(1, Pair valterm_emptyset),
      (i, random j \<circ>\<rightarrow> (%x. random_aux_set (i - 1) j \<circ>\<rightarrow> (%s. Pair (valtermify_insert x s))))])"
proof (induct i rule: natural.induct)
  case zero
  show ?case by (subst select_weight_drop_zero [symmetric])
    (simp add: random_aux_set.simps [simplified] less_natural_def)
next
  case (Suc i)
  show ?case by (simp only: random_aux_set.simps(2) [of "i"] Suc_natural_minus_one)
qed

definition "random_set i = random_aux_set i i"

instance ..

end

end

lemma random_aux_rec:
  fixes random_aux :: "natural \<Rightarrow> 'a"
  assumes "random_aux 0 = rhs 0"
    and "\<And>k. random_aux (Code_Numeral.Suc k) = rhs (Code_Numeral.Suc k)"
  shows "random_aux k = rhs k"
  using assms by (rule natural.induct)*)

(*subsection \<open>Deriving random generators for datatypes\<close>

ML_file \<open>Tools/Quickcheck/quickcheck_common.ML\<close>
ML_file \<open>Tools/Quickcheck/random_generators.ML\<close>


subsection \<open>Code setup\<close>

code_printing
  constant random_fun_aux \<rightharpoonup> (Quickcheck) "Random'_Generators.random'_fun"
  \<comment> \<open>With enough criminal energy this can be abused to derive \<^prop>\<open>False\<close>;
  for this reason we use a distinguished target \<open>Quickcheck\<close>
  not spoiling the regular trusted code generation\<close>

code_reserved Quickcheck Random_Generators*)

hide_const (open) (*catch_match*) random (*collapse beyond*) random_fun_aux random_fun_lift

hide_fact (open) (*collapse_def beyond_def*) random_fun_lift_def



subsection \<open>Continuation passing style functions as plus monad\<close>

type_synonym 'a cps = "('a \<Rightarrow> term list option) \<Rightarrow> term list option"

definition cps_empty :: "'a cps"
  where "cps_empty = (\<lambda>cont. None)"

definition cps_single :: "'a \<Rightarrow> 'a cps"
  where "cps_single v = (\<lambda>cont. cont v)"

definition cps_bind :: "'a cps \<Rightarrow> ('a \<Rightarrow> 'b cps) \<Rightarrow> 'b cps"
  where "cps_bind m f = (\<lambda>cont. m (\<lambda>a. (f a) cont))"

definition cps_plus :: "'a cps \<Rightarrow> 'a cps \<Rightarrow> 'a cps"
  where "cps_plus a b = (\<lambda>c. case a c of None \<Rightarrow> b c | Some x \<Rightarrow> Some x)"

definition cps_if :: "bool \<Rightarrow> unit cps"
  where "cps_if b = (if b then cps_single () else cps_empty)"

definition cps_not :: "unit cps \<Rightarrow> unit cps"
  where "cps_not n = (\<lambda>c. case n (\<lambda>u. Some []) of None \<Rightarrow> c () | Some _ \<Rightarrow> None)"

type_synonym 'a pos_bound_cps =
  "('a \<Rightarrow> (bool * term list) option) \<Rightarrow> natural \<Rightarrow> (bool * term list) option"

definition pos_bound_cps_empty :: "'a pos_bound_cps"
  where "pos_bound_cps_empty = (\<lambda>cont i. None)"

definition pos_bound_cps_single :: "'a \<Rightarrow> 'a pos_bound_cps"
  where "pos_bound_cps_single v = (\<lambda>cont i. cont v)"

definition pos_bound_cps_bind :: "'a pos_bound_cps \<Rightarrow> ('a \<Rightarrow> 'b pos_bound_cps) \<Rightarrow> 'b pos_bound_cps"
  where "pos_bound_cps_bind m f = (\<lambda>cont i. if i = 0 then None else (m (\<lambda>a. (f a) cont i) (i - 1)))"

definition pos_bound_cps_plus :: "'a pos_bound_cps \<Rightarrow> 'a pos_bound_cps \<Rightarrow> 'a pos_bound_cps"
  where "pos_bound_cps_plus a b = (\<lambda>c i. case a c i of None \<Rightarrow> b c i | Some x \<Rightarrow> Some x)"

definition pos_bound_cps_if :: "bool \<Rightarrow> unit pos_bound_cps"
  where "pos_bound_cps_if b = (if b then pos_bound_cps_single () else pos_bound_cps_empty)"

datatype (plugins only: code extraction) (dead 'a) unknown =
  Unknown | Known 'a

datatype (plugins only: code extraction) (dead 'a) three_valued =
  Unknown_value | Value 'a | No_value

type_synonym 'a neg_bound_cps =
  "('a unknown \<Rightarrow> term list three_valued) \<Rightarrow> natural \<Rightarrow> term list three_valued"

definition neg_bound_cps_empty :: "'a neg_bound_cps"
  where "neg_bound_cps_empty = (\<lambda>cont i. No_value)"

definition neg_bound_cps_single :: "'a \<Rightarrow> 'a neg_bound_cps"
  where "neg_bound_cps_single v = (\<lambda>cont i. cont (Known v))"

definition neg_bound_cps_bind :: "'a neg_bound_cps \<Rightarrow> ('a \<Rightarrow> 'b neg_bound_cps) \<Rightarrow> 'b neg_bound_cps"
  where "neg_bound_cps_bind m f =
    (\<lambda>cont i.
      if i = 0 then cont Unknown
      else m (\<lambda>a. case a of Unknown \<Rightarrow> cont Unknown | Known a' \<Rightarrow> f a' cont i) (i - 1))"

definition neg_bound_cps_plus :: "'a neg_bound_cps \<Rightarrow> 'a neg_bound_cps \<Rightarrow> 'a neg_bound_cps"
  where "neg_bound_cps_plus a b =
    (\<lambda>c i.
      case a c i of
        No_value \<Rightarrow> b c i
      | Value x \<Rightarrow> Value x
      | Unknown_value \<Rightarrow>
          (case b c i of
            No_value \<Rightarrow> Unknown_value
          | Value x \<Rightarrow> Value x
          | Unknown_value \<Rightarrow> Unknown_value))"

definition neg_bound_cps_if :: "bool \<Rightarrow> unit neg_bound_cps"
  where "neg_bound_cps_if b = (if b then neg_bound_cps_single () else neg_bound_cps_empty)"

definition neg_bound_cps_not :: "unit pos_bound_cps \<Rightarrow> unit neg_bound_cps"
  where "neg_bound_cps_not n =
    (\<lambda>c i. case n (\<lambda>u. Some (True, [])) i of None \<Rightarrow> c (Known ()) | Some _ \<Rightarrow> No_value)"

definition pos_bound_cps_not :: "unit neg_bound_cps \<Rightarrow> unit pos_bound_cps"
  where "pos_bound_cps_not n =
    (\<lambda>c i. case n (\<lambda>u. Value []) i of No_value \<Rightarrow> c () | Value _ \<Rightarrow> None | Unknown_value \<Rightarrow> None)"

hide_type (open) cps pos_bound_cps neg_bound_cps unknown three_valued

hide_const (open) cps_empty cps_single cps_bind cps_plus cps_if cps_not
  pos_bound_cps_empty pos_bound_cps_single pos_bound_cps_bind
  pos_bound_cps_plus pos_bound_cps_if pos_bound_cps_not
  neg_bound_cps_empty neg_bound_cps_single neg_bound_cps_bind
  neg_bound_cps_plus neg_bound_cps_if neg_bound_cps_not
  Unknown Known Unknown_value Value No_value

class exhaustive = term_of +
  fixes exhaustive :: "('a \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"

class full_exhaustive = term_of +
  fixes full_exhaustive ::
    "('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"



end
