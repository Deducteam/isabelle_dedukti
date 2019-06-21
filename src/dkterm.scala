package isabelle.dedukti

import isabelle._

object Dkterm
{
  sealed abstract class Term
  case class Kind() extends Term
  // "KIND" constant
  case class Type() extends Term
  // "TYPE" constant
  case class Symb(name: String,
    sym_type: Term,
    sym_def: Option[Term]) extends Term
  // User defined symbol
  case class Abst(dom: Term) extends Term
  // Abstraction with domain type
  // FIXME binder
  case class Vari(name: String) extends Term
  // Free variable
  case class Prod(arg: Term) extends Term
  // Dependent product
  // FIXME binder
  case class Appl(u: Term, v: Term) extends Term
  // Application of u to v
}
