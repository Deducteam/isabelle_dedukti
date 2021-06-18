/** Abstract syntax for lambda-Pi calculus **/


package isabelle.dedukti

import isabelle._


object Syntax
{
  type Ident = String

  sealed abstract class Term
  type Typ = Term
  sealed case class Arg(id: Option[Ident], typ: Option[Typ])

  case object TYPE extends Term
  case  class Symb(id: Ident) extends Term
  case  class FVar(id: Ident) extends Term
  case  class BVar(idx: Int) extends Term
  case  class Appl(t1: Term, t2: Term) extends Term
  case  class Abst(arg: Arg, t: Term) extends Term
  case  class Prod(arg: Arg, t: Term) extends Term

  def arrow(ty: Typ, tm: Term): Term = Prod(Arg(None, Some(ty)), tm)

  def appls(head: Term, spine: List[Term]): Term = spine.foldLeft(head)(Appl)
  def arrows(tys: List[Typ], tm: Term): Term =  tys.foldRight(tm)(arrow)

  def dest_appls(t: Term, args: List[Term]): (Term, List[Term]) =
    t match {
      case Syntax.Appl(t1, t2) => dest_appls(t1, args = t2 :: args)
      case t => (t, args)
    }

  sealed abstract class Command
  case class Rewrite(vars: List[Ident], lhs: Term, rhs: Term) extends Command
  case class Declaration(id: Ident, args: List[Arg], ty: Typ, const: Boolean = true) extends Command
  case class Definition(id: Ident, args: List[Arg], ty: Option[Typ], tm: Term) extends Command
  case class Theorem(id: Ident, args: List[Arg], ty: Typ, prf: Term) extends Command
}
