/** Abstract syntax suitable for both Dedukti (2.7) and lambdapi calculus **/

package isabelle.dedukti

import scala.annotation.tailrec
import isabelle._


object Syntax {
  /** A <span style="color:#9932CC;"> dk/lp </span> identifier. */
  type Ident = String

/** <span style="color:#9932CC;"> dk/lp </span> terms. */
  sealed abstract class Term
  /** Alias for <span style="color:#9932CC;"> dk/lp </span> terms, specifically used for types. */
  type Typ = Term

  /** A <span style="color:#9932CC"> dk/lp </span> binder for variables and function arguments.
   * @param id the identifier of the variable/argument. <code>None</code> if anonymous
   * @param typ the type of the variable/argument */
  sealed case class BoundArg(
    id: Option[Ident],
    typ: Typ/*,
    implicit_arg: Boolean = false*/)

  /** The <span style="color:#9932CC;"> dk/lp </span> sort
   * <code><span style="color:#87CEFA">TYPE</span></code> of all types. */
  case object TYPE extends Term
  /** A <span style="color:#9932CC;"> dk/lp </span> reference to a declared symbol.
   * @param id the name of the symbol */
  case  class Symb(id: Ident) extends Term
  /** A <span style="color:#9932CC;"> dk/lp </span> reference to a named binder
   * @param id the name of the binder */
  case  class  Var(id: Ident) extends Term
  // Tools for implicit arguments will be in comments in case they become
  // usable again.
  /** The <span style="color:#9932CC;"> dk/lp </span> application
   * <code><span style="color:#87CEFA"> t1 t2</span></code>
   * @param t1 the function that is applied
   * @param t2 the term that it is applied to */
  case  class Appl(t1: Term, t2: Term/*, isImplicit: Boolean = false*/) extends Term
  /** The <span style="color:#9932CC;"> dk/lp </span> anonymous function
   * <code><span style="color:#87CEFA"> λ arg, t</span></code> mapping
   * <code><i><span style="color:#FFC0CB"> arg</span></i></code> to
   * <code><i><span style="color:#FFC0CB"> t</span></i></code>.
   * @param arg the argument of the function
   * @param t the body of the function */
  case  class Abst(arg: BoundArg, t: Term) extends Term
  /** The <span style="color:#9932CC;"> dk/lp </span> dependent product
   * <code><span style="color:#87CEFA"> Π arg, t</span></code>.
   * @param arg the argument of the product
   * @param t the return type, possibly parametrized by
   *          <code><i><span style="color:#FFC0CB;"> arg</span></i></code>*/
  case  class Prod(arg: BoundArg, t: Typ) extends Term

  /** The <span style="color:#9932CC;"> dk/lp </span> non-dependent product
   * <code><span style="color:#87CEFA"> ty → tm</span></code>.
   * @param ty the domain type
   * @param tm the co-domain type
   * @return the non-dependent product <br>
   *         <code><span style="color:#87CEFA"> ty → tm</span></code>. <br>
   *         Syntactic sugar for <code><span style="color:#87CEFA"> Π x:ty, tm</span></code>
   *         when <code><i> <span style="color:#FFC0CB;"> x</span></i></code> does not occur in
   *         <code><i> <span style="color:#FFC0CB;"> ty</span></i></code>.*/
  def arrow(ty: Typ, tm: Typ): Typ = Prod(BoundArg(None, ty), tm)

  /** <code><span style="color:#FFA500;"> appls</span>(<i><span style="color:#FFC0CB;">head</span></i>,
     *[<i><span style="color:#FFC0CB;">x1</span></i>, ..., <i><span style="color:#FFC0CB;">xn</span></i>])</code>
   * is the <span style="color:#9932CC;"> dk/lp </span> <br> chained application
   * <code><span style="color:#87CEFA"> head x1 ... xn</span></code>.
   * @param head the curried function that is applied
   * @param spine the list of arguments that the function is applied to
   * @return the term which results from applying
   *         <code><i><span style="color:#FFC0CB;">head</span></i></code>
   *         to each argument in <code><i><span style="color:#FFC0CB;">spine</span></i></code>.*/
  @tailrec
  def appls(head: Term, spine: List[Term]): Term = // += impl: List[Boolean]
    /* (spine, impl) match {
      case (Nil, impl) if impl.exists(identity) => isabelle.error("Missing implicit argument")
      case (Nil, _) => head
      case (arg :: spine, impl :: impls) => appls(Appl(head, arg, impl), spine, impls)
      case (spine, Nil) => spine.foldLeft(head)(Appl(_, _))
    } */
    spine.foldLeft(head)(Appl(_,_))

  /** <code><span style="color:#FFA500;"> arrows</span>([<i><span style="color:#FFC0CB;">T1</span></i>,
     ...,<i><span style="color:#FFC0CB;"> Tn</span></i>], <i><span style="color:#FFC0CB;">tm</span></i>)</code>
   * is the <span style="color:#9932CC;"> dk/lp </span> <br> chained arrow type
   * <code><span style="color:#87CEFA"> T1 → ... → Tn → tm</span></code>.
   * @param tys the list of domain types
   * @param tm the co-domain type
   * @return the type of curried functions with arguments in
   *         <code><i><span style="color:#FFC0CB;">tys</span></i></code> and return type
   *         <code><i><span style="color:#FFC0CB;">tm</span></i></code>*/
  def arrows(tys: List[Typ], tm: Typ): Typ = tys.foldRight(tm)(arrow)

  /** <code><span style="color:#FFA500;"> destruct_appls</span>(<span style="color:#FFA500;">appls</span>(<i><span style="color:#FFC0CB;">head</span></i>,
     <i> <span style="color:#FFC0CB;"> spine</span></i>))=(<i><span style="color:#FFC0CB;">head</span></i>,
     <i> <span style="color:#FFC0CB;"> spine</span></i>)</code>
   * <br> Recursively splits a <span style="color:#9932CC;"> dk/lp </span> term between its head and its arguments.
   * @param t the term being split
   * @param args the list of arguments encountered so far (default: <code>Nil</code>)
   * @return the couple of the head function and the list of arguments it is applied to*/
  @tailrec
  def destruct_appls(t: Term, args: List[Term] = Nil): (Term, List[Term]) = //List[Term]->List[(Term,Boolean)]
    t match {
      case Syntax.Appl(t1, t2/*, b*/) => destruct_appls(t1, args = /*(*/t2/*, b)*/ :: args)
      case t => (t, args)
    }

  /** Data about a <span style="color:#9932CC;"> lambdapi </span> notation. */
  sealed abstract class Notation
  /** A prefix <span style="color:#9932CC;"> lambdapi </span> notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class Prefix(op: Ident, priority: Double) extends Notation
  /** A non-associative infix <span style="color:#9932CC;"> lambdapi </span> notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class Infix (op: Ident, priority: Double) extends Notation
  /** A left-associative infix <span style="color:#9932CC;"> lambdapi </span> notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class InfixL(op: Ident, priority: Double) extends Notation
  /** A right-associative prefix <span style="color:#9932CC;"> lambdapi </span> notation.
   * @param op the identifier of the function for which this notation is defined
   * @param priority the priority of the notation (not necessarily an integer). */
  case class InfixR(op: Ident, priority: Double) extends Notation
  /** Quantifier-like <span style="color:#9932CC;"> lambdapi </span> notation.
   * Allows to write {@code <span style="color:#87CEFA"> `op x, t</span>} <br>
   * instead of {@code <span style="color:#87CEFA"> op(λ x, t)</span>}.
   * @param op the identifier of the function for which this notation is defined*/
  case class Quantifier(op: Ident) extends Notation

  /** The priority of a <span style="color:#9932CC;"> lambdapi </span>
   * notation.
   * @param not the notation to be inspected
   * @return the floating-point priority of the notation.
   *         If <code><i><span style="color:#FFC0CB;">not</span></i></code>
   *         is a quantifier-like notation, it has no priority and thus
   *         <code><span style="color:#FFA500;">getPriority</span>(<i><span style="color:#FFC0CB;">var</span></i>)</code>
   *         returns <code>None</code> */
  def getPriority(not: Notation): Option[Double] =
    not match {
      case Prefix(_, priority) => Some(priority)
      case Infix (_, priority) => Some(priority)
      case InfixL(_, priority) => Some(priority)
      case InfixR(_, priority) => Some(priority)
      case Quantifier(_) => None
    }

  /** Returns the function for which a <span style="color:#9932CC;"> lambdapi </span> notation is defined.
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

  /** The internal <span style="color:#9932CC;">lambdapi</span>
   * notation for function application {@link Appl}.*/
  val appNotation: Notation = InfixL(" ", Double.PositiveInfinity)
  /** TODO: Understand */
  val justHadPars: Notation = Infix("()", Double.NegativeInfinity)
  /** The internal <span style="color:#9932CC;">lambdapi</span> notation for arrow types
   * {@link arrow} */
  val arrNotation: Notation = InfixR("→", -2)
  /** The <span style="color:#9932CC;">lambdapi</span> notation for single-argument
   * lambda abstraction {@link Abst}.  */
  val absNotation: Notation = InfixR("λ", -1)
  val defaultPrefixPriority = 10.0

  /** A <span style="color:#9932CC;">dk/lp</span> command. */
  sealed abstract class Command
  /** <code><span style="color:#87CEFA">constant symbol id (args) : ty;( notation not;)</span></code><br>
   * Command declaring a <span style="color:#9932CC;">lambdapi</span> constructor symbol.
   * @param id the identifier of the symbol
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to a product
   *             <code><span style="color:#87CEFA">Π args, ty</span></code>)
   * @param ty the type of the symbol
   * @param not an optional notation for the symbol (default: <code>None</code>) */
  case class Declaration(id: Ident, args: List[BoundArg], ty: Typ, not: Option[Notation] = None) extends Command
  /** TODO: Why is there no argument list? <br>
   * <code><span style="color:#87CEFA">(injective )symbol id : ty;( notation not;)</span></code><br>
   * Command declaring a definable <span style="color:#9932CC;">dk/lp</span> symbol.
   * @param id the identifier of the symbol
   * @param ty the type of the symbol
   * @param inj a boolean value expressing whether the symbol is injective or not <br>
   *            (<span style="color:#9932CC;">lambdapi</span> exclusive)
   * @param not an optional <span style="color:#9932CC;">lambdapi</span>
   *            notation for the symbol (default: <code>None</code>)*/
  case class DefableDecl(id: Ident, ty: Typ, inj: Boolean = false, not: Option[Notation] = None) extends Command
  /** <code><span style="color:#87CEFA">constant symbol id (args) : ty ≔ tm;( notation not;)</span></code><br>
   * Command declaring a <span style="color:#9932CC;">dk/lp</span> symbol with a definition.
   *
   * @param id   the identifier of the symbol
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to a product
   *             <code><span style="color:#87CEFA">Π args, ty</span></code>)
   * @param ty   the optional type of the symbol. If not provided, can be inferred from the body
   * @param tm   the body of the symbol
   * @param not  an optional <span style="color:#9932CC;">lambdapi</span>
   *             notation for the symbol (default: <code>None</code>) */
  case class Definition (id: Ident, args: List[BoundArg], ty: Option[Typ],
                          tm: Term, not: Option[Notation] = None) extends Command
  /** <code><span style="color:#87CEFA">opaque symbol id (args) : ty ≔ prf</span></code><br>
   * Command declaring a <span style="color:#9932CC;">dk/lp</span> theorem.
   * @param id   the identifier of the theorem
   * @param args the list of arguments of the type of the symbol <br>
   *             (equivalent to being universally quantified)
   * @param ty   the type of the symbol, which is the statement of the theorem
   * @param prf  the body of the symbol, which is the proof of the theorem */
  case class Theorem(id: Ident, args: List[BoundArg], ty: Typ, prf: Term) extends Command
  /** <code><span style="color:#87CEFA">rule lhs($x, $y, ...) ↪ rhs($x, $y, ...);</span></code><br>
   *  <span style="color:#9932CC;">dk/lp</span> command declaring a rewrite rule.
   *  @param vars the list of pattern variables to be instantiated, declared
   *              before the rule in <span style="color:#9932CC;">dedukti</span>
   *              and used with a dollar sign in
   *              <span style="color:#9932CC;">lambdapi</span>
   *  @param lhs the left-hand side of the rewrite rule, to be matched in order to be rewritten
   *  @param rhs the right-hand side of the rewrite rule, to be rewritten to */
  case class Rewrite(vars: List[Ident], lhs: Term, rhs: Term) extends Command
}
