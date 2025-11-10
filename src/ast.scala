/** Abstract syntax suitable for both Dedukti (2.7) and lambdapi calculus **/

package isabelle.dedukti

import scala.annotation.tailrec
import isabelle._

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference dedukti (purple)
 *       $lp: reference lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define mete /span></code
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
object Syntax {
  /** A $dklp identifier. */
  type Ident = String

/** $dklp terms. */
  sealed abstract class Term
  /** Alias for $dklp terms, specifically used for types. */
  type Typ = Term

  /** A $dklp binder for variables and function arguments.
   * @param id the identifier of the variable/argument. <$met>None<$mete> if anonymous
   * @param typ the type of the variable/argument 
   * @param implicit_arg true if this is an implicit argument (default: <code>false</code>) */
  sealed case class BoundArg(
    id: Option[Ident],
    typ: Typ,
    implicit_arg: Boolean = false)

  /** The $dklp sort
   * <$lpc>TYPE<$lpce> of all types. */
  case object TYPE extends Term
  /** A $dklp reference to a declared symbol.
   * @param id the name of the symbol */
  case  class Symb(id: Ident) extends Term
  /** A $dklp reference to a named binder
   * @param id the name of the binder */
  case  class  Var(id: Ident) extends Term
  /** The $dklp application <$lpc>t1 t2<$lpce>
   * @param t1 the function that is applied
   * @param t2 the term that it is applied to
   * @param isImplicit true if t2 should be implicit (can be either written with [] or not written at all).
   *                   Default: <code>false</code> */
  case  class Appl(t1: Term, t2: Term, isImplicit: Boolean = false) extends Term
  /** The $dklp anonymous function <$lpc> λ arg, t<$lpce> mapping <$arg>arg<$arge> to <$arg>t<$arge>.
   * @param arg the argument of the function
   * @param t the body of the function*/
  case  class Abst(arg: BoundArg, t: Term) extends Term
  /** The $dklp dependent product <$lpc>Π arg, t<$lpce>.
   * @param arg the argument of the product
   * @param t the return type, possibly parametrized by <$arg>arg<$arge>*/
  case  class Prod(arg: BoundArg, t: Typ) extends Term

  /** The $dklp non-dependent product <$lpc>ty → tm<$lpce>.
   * @param ty the domain type
   * @param tm the co-domain type
   * @return the non-dependent product <$lpc>ty → tm<$lpce>. <br>
   *         Syntactic sugar for <$lpc> Π x:ty, tm<$lpce> when <$lpc>x<$lpce>
   *         does not occur in <$lpc>ty<$lpce>.*/
  def arrow(ty: Typ, tm: Typ): Typ = Prod(BoundArg(None, ty), tm)

  /** <code><$met>appls<$mete>(<$arg>head<$arge>,[<$arg>x1<$arge>, ..., <$arg>xn<$arge>])</code>
   * is the $dklp chained application <$lpc>head x1 ... xn<$lpce>.
   * @param head the curried function that is applied
   * @param spine the list of arguments that the function is applied to
   * @param impl <$arg>impl<$arge>(i) is true if <$arg>spine<$arge>(i) is an implicit argument
   * @return the term which results from applying <$arg>head<$arge>
   *         to each argument in <$arg>spine<$arge>.*/
  @tailrec
  def appls(head: Term, spine: List[Term], impl: List[Boolean]): Term =
    (spine, impl) match {
      case (_, Nil) => spine.foldLeft(head)(Appl(_,_,false))
      case (arg :: spine, impl :: impls) => appls(Appl(head, arg, impl), spine, impls)
      case _ => isabelle.error("Missing implicit argument")
    }

  /** <code><$met>arrows<$mete>([<$arg>T1<$arge>, ..., <$arg>Tn<$arge>], <$arg>tm<$arge>)</code>
   * is the $dklp chained arrow type <$lpc>T1 → ... → Tn → tm<$lpce>.
   * @param tys the list of domain types
   * @param tm the co-domain type
   * @return the type of curried functions with arguments in
   *         <$arg>tys<$arge> and return type <$arg>tm<$arge>*/
  def arrows(tys: List[Typ], tm: Typ): Typ = tys.foldRight(tm)(arrow)

  /** <code><$met>destruct_appls<$mete>(<$met>appls<$mete>(<$arg>head<$arge>,
   * <$arg>spine<$arge>))=(<$arg>head<$arge>,<$arg>spine<$arge>)</code> <br>
   * Recursively splits a $dklp term between its head and its arguments.
   * 
   * @param t the term being split
   * @param args the list of arguments encountered so far (default: <code>Nil</code>)
   *             
   * @return the couple of the head function and the list of arguments it is applied to
   * 
   * @see <$met><u>[[Exporter.head_args]]</u><$mete> for $isa terms
   */
  @tailrec
  def destruct_appls(t: Term, args: List[(Term,Boolean)] = Nil): (Term, List[(Term,Boolean)]) =
    t match {
      case Syntax.Appl(t1, t2, b) => destruct_appls(t1, args = (t2, b) :: args)
      case t => (t, args)
    }

  /** Data about a $lp notation. */
  sealed abstract class Notation
  /** A prefix $lp notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class Prefix(op: Ident, priority: Double) extends Notation
  /** A non-associative infix $lp notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class Infix (op: Ident, priority: Double) extends Notation
  /** A left-associative infix $lp notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class InfixL(op: Ident, priority: Double) extends Notation
  /** A right-associative prefix $lp notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class InfixR(op: Ident, priority: Double) extends Notation
  /** Quantifier-like $lp notation.
   * Allows to write <$lpc>&#96;op x, t<$lpce> instead of <$lpc>op(λ x, t)<$lpce>.
   * @param op the identifier of the function for which this notation is defined*/
  case class Quantifier(op: Ident) extends Notation

  /** The priority of a $lp
   * notation.
   * @param not the notation to be inspected
   * @return the floating-point priority of the notation. If <$arg>not<$arge>
   *         is a quantifier-like notation, it has no priority and thus
   *         <code><$met>getPriority<$mete>(<$arg>not<$arge>)</code>
   *         returns <$met>None<$mete> */
  def getPriority(not: Notation): Option[Double] =
    not match {
      case Prefix(_, priority) => Some(priority)
      case Infix (_, priority) => Some(priority)
      case InfixL(_, priority) => Some(priority)
      case InfixR(_, priority) => Some(priority)
      case Quantifier(_) => None
    }

  /** Returns the function for which a $lp notation is defined.
   * @param not the notation to be inspected
   * @return the identifier of the function for which the notation is defined */
  def getOperator(not: Notation): Ident =
    not match {
      case Prefix(op, _) => op
      case Infix (op, _) => op
      case InfixL(op, _) => op
      case InfixR(op, _) => op
      case Quantifier(op) => op
    }

  /** $lp notation representing function application [[Appl]].
   *  Used for decision of parenthesising, as it is left associative and
   *  has priority +∞
   */
  val appNotation: Notation = InfixL(" ", Double.PositiveInfinity)
  /** $lp notation representing the fact that there is no notation.
   *  Used for decision of parenthesising, as it is non-associative and
   *  has priority -∞
   */
  val justHadPars: Notation = Infix("()", Double.NegativeInfinity)
  /** $lp notation representing arrow types [[arrow]].
   * Used for Decision of parenthesising, as it is non-associative and has priority -1. */
  val arrNotation: Notation = InfixR("→", -2)
  /** $lp notation representing single-argument lambda abstraction [[Abst]].
   *  Used for decision of parenthesising, as it is right associative and has
   *  priority -1 */
  val absNotation: Notation = InfixR("λ", -1)
  /** Has value 10.0. */
  val defaultPrefixPriority = 10.0

  /** A $dklp command relevant to this library. */
  sealed abstract class Command
  /** <$lpc>constant symbol id (args) : ty;( notation not;)<$lpce><br>
   * Command declaring a $lp constructor symbol.
   * @param id the identifier of the symbol
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to a product <$lpc>Π args, ty<$lpce>)
   * @param ty the type of the symbol
   * @param not an optional notation for the symbol (default: <$met>None<$mete>)
   */
  case class Declaration(id: Ident, args: List[BoundArg], ty: Typ, not: Option[Notation] = None) extends Command
  /** <$lpc>(injective )symbol id : ty;( notation not;)<$lpce>
   * Command declaring a definable $dklp symbol.
   * @param id the identifier of the symbol
   * @param ty the type of the symbol
   * @param inj a boolean value expressing whether the symbol is injective or not <br>
   *            ($lp exclusive)
   * @param not an optional $lp notation for the symbol (default: <$met>None<$mete>)
   */
  case class DefableDecl(id: Ident, ty: Typ, inj: Boolean = false, not: Option[Notation] = None) extends Command
  /** <$lpc>constant symbol id (args) : ty ≔ tm;( notation not;)<$lpce>
   * Command declaring a $dklp symbol with a definition.
   *
   * @param id   the identifier of the symbol
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to a product <$lpc>Π args, ty<$lpce>)
   * @param ty   the optional type of the symbol. If not provided, can be inferred from the body
   * @param tm   the body of the symbol
   * @param not  an optional $lp
   *             notation for the symbol (default: <$mete>None<$mete>) */
  case class Definition (id: Ident, args: List[BoundArg], ty: Option[Typ],
                          tm: Term, not: Option[Notation] = None) extends Command
  /** <$lpc>opaque symbol id (args)(: ty )≔ prf<$lpce>
   * Command declaring a $dklp theorem.
   * @param id   the identifier of the theorem
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to being universally quantified)
   * @param ty   the type of the symbol, which is the statement of the theorem
   * @param prf  the body of the symbol, which is the proof of the theorem */
  case class Theorem(id: Ident, args: List[BoundArg], ty: Typ, prf: Term) extends Command
  /** <$lpc>rule lhs($x, $y, ...) ↪ rhs($x, $y, ...);<$lpce>
   *  $dklp command declaring a rewrite rule.
   *  @param vars the list of pattern variables to be instantiated, declared
   *              before the rule in $dk and used with a dollar sign in $lp
   *  @param lhs the left-hand side of the rewrite rule, to be matched in order to be rewritten
   *  @param rhs the right-hand side of the rewrite rule, to be rewritten to */
  case class Rewrite(vars: List[Ident], lhs: Term, rhs: Term) extends Command
}
