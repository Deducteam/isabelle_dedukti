package isabelle.dedukti

import isabelle._

object Dkterm
{
  sealed abstract class Term
  case class Kind() extends Term
  // "KIND" constant
  case class Type() extends Term
  {
    override def toString(): String = "TYPE"
  }
  // "TYPE" constant
  case class Vari(name: String) extends Term
  {
    override def toString(): String = name
  }
  // Free variable
  case class Symb(name: String,
    sym_type: Term,
    sym_def: Option[Term]) extends Term
  // User defined symbol
  case class Abst(bvar: Term, dom: Term, body: Term) extends Term
  // Abstraction with domain type
  case class Prod(bvar: Term, dom: Term, body: Term) extends Term
  // Dependent product
  case class Appl(u: Term, v: Term) extends Term
  // Application of u to v
}
