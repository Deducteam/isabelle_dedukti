section \<open>Basic examples involving proof terms\<close>

theory Ex_HOL
  imports "HOL-Isar_Examples.First_Order_Logic"
begin

lemma ex: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then obtain B and A ..
  then show "B \<and> A" ..
qed

ML_val \<open>
  val thm = @{thm ex};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {name, ...} => insert (op =) name) [body] [];
\<close>

text \<open>
  The result refers to various basic facts of Isabelle/HOL: @{thm [source]
  impI}, @{thm [source] conjE}, @{thm [source] conjI} etc. The
  combinator \<^ML>\<open>Proofterm.fold_body_thms\<close> recursively explores the graph of
  the proofs of all theorems being used here.

  \<^medskip>
  Alternatively, we may produce a proof term manually, and turn it into a
  theorem as follows:
\<close>

ML_val \<open>
  val thy = \<^theory>;
  val ctxt = \<^context>;
  val prf =
    Proof_Syntax.read_proof thy true false
      "impI \<cdot> _ \<cdot> _ \<bullet> \
      \   (\<^bold>\<lambda>H: _. \
      \     conjE \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> H \<bullet> \
      \       (\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H))";
  val thm =
    Proofterm.reconstruct_proof thy \<^prop>\<open>A \<and> B \<longrightarrow> B \<and> A\<close> prf
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
\<close>

end
