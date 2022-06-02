session Dedukti_Example in "Ex/Example" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions
    "Pure-Examples"
  theories
    "Pure-Examples.First_Order_Logic"
    "Pure-Examples.Higher_Order_Logic"

session Dedukti_Base in "Ex/Base" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Inductive

session Dedukti_Min in "Ex/Min" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.HOL

session Dedukti_All in "Ex/All" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Complex_Main

session Dedukti_Essential in "Ex/Essential" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.BNF_Greatest_Fixpoint
    HOL.Binomial
    HOL.Conditionally_Complete_Lattices
    HOL.Extraction
    HOL.Filter

session Dedukti_Presburger_deps in "Ex/Presburger_deps" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Groebner_Basis HOL.Set_Interval


session Dedukti_Presburger in "Ex/Presburger" = Dedukti_Presburger_deps +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Presburger

session Dedukti_HOL in "Ex/HOL" = Pure +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.HOL
    Tools.Code_Generator

session Dedukti_Orderings in "Ex/Orderings" = Dedukti_HOL +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Orderings

session Dedukti_Groups in "Ex/Groups" = Dedukti_Orderings +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Groups

session Dedukti_Set in "Ex/Set" = Dedukti_Groups +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Set

session Dedukti_Fun in "Ex/Fun" = Dedukti_Set +
  options [export_theory, export_proofs, record_proofs = 2]
  sessions HOL
  theories
    HOL.Fun
