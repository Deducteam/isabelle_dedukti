/** Abstract syntax for lambda-Pi calculus **/


package isabelle.dedukti

import scala.annotation.tailrec
import isabelle._


object Syntax
{
  type Ident = String

  sealed abstract class Term
  type Typ = Term
  sealed case class BoundArg(
    id: Option[Ident],
    typ: Option[Typ],
    implicit_arg: Boolean = false)

  case object TYPE extends Term
  case  class Symb(id: Ident) extends Term
  case  class  Var(id: Ident) extends Term
  case  class Appl(t1: Term, t2: Term, isImplicit: Boolean = false) extends Term
  case  class Abst(arg: BoundArg, t: Term) extends Term
  case  class Prod(arg: BoundArg, t: Term) extends Term

  def arrow(ty: Typ, tm: Term): Term = Prod(BoundArg(None, Some(ty)), tm)

  // No fold_left2, no recursive destructuring on function arguments... Better off doing it manually
  @tailrec
  def appls(head: Term, spine: List[Term], impl: List[Boolean]): Term =
  (spine, impl) match {
    case (Nil, impl) if impl.exists(identity) => isabelle.error("Missing implicit argument")
    case (Nil, _) => head
    case (arg :: spine, impl :: impls) => appls(Appl(head, arg, impl), spine, impls)
    case (spine, Nil) => spine.foldLeft(head)(Appl(_, _))
  }

  def arrows(tys: List[Typ], tm: Term): Term = tys.foldRight(tm)(arrow)

  @tailrec
  def destruct_appls(t: Term, args: List[(Term, Boolean)] = Nil): (Term, List[(Term, Boolean)]) =
    t match {
      case Syntax.Appl(t1, t2, b) => destruct_appls(t1, args = (t2, b) :: args)
      case t => (t, args)
    }

  sealed abstract class Notation
  case class Prefix(op: Ident, priority: Float) extends Notation
  case class Infix (op: Ident, priority: Float) extends Notation
  case class InfixL(op: Ident, priority: Float) extends Notation
  case class InfixR(op: Ident, priority: Float) extends Notation
  case class Quantifier(op: Ident) extends Notation

  def getPriority(not: Notation): Option[Float] =
    not match {
      case Prefix(_, priority) => Some(priority)
      case Infix (_, priority) => Some(priority)
      case InfixL(_, priority) => Some(priority)
      case InfixR(_, priority) => Some(priority)
      case Quantifier(_) => None
    }

  def getOperator(not: Notation): Ident =
    not match {
      case Prefix(op, _) => op
      case Infix (op, _) => op
      case InfixL(op, _) => op
      case InfixR(op, _) => op
      case Quantifier(op) => op
    }

  val appNotation: Notation = InfixL(" ", Float.PositiveInfinity)
  val justHadPars: Notation = Infix("()", Float.NegativeInfinity)
  val arrNotation: Notation = InfixR("→", -2)
  val absNotation: Notation = InfixR("λ", -1)
  val defaultPrefixPriority = 10

  sealed abstract class Command
  case class Declaration(id: Ident, args: List[BoundArg], ty: Typ, not: Option[Notation] = None) extends Command
  case class DefableDecl(id: Ident, ty: Typ, inj: Boolean = false, not: Option[Notation] = None) extends Command
  case class Definition (id: Ident, args: List[BoundArg], ty: Option[Typ],
                          tm: Term, not: Option[Notation] = None) extends Command
  case class Theorem(id: Ident, args: List[BoundArg], ty: Typ, prf: Term) extends Command
  case class Rewrite(vars: List[Ident], lhs: Term, rhs: Term) extends Command
}
