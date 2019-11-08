/** Dedukti lp syntax **/
// see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf

package isabelle.dedukti


import isabelle._

import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter, Writer}


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

  def arrow(ty: Typ, tm: Term) = Prod(Arg(None, Some(ty)), tm)

  def appls(head: Term, spine: List[Term]): Term = spine.foldLeft(head)(Appl)
  def arrows(tys: List[Typ], tm: Term): Term =  tys.foldRight(tm)(arrow)

  sealed abstract class Command
  case class Rewrite(vars: List[Ident], lhs: Term, rhs: Term) extends Command
  case class Declaration(id: Ident, args: List[Arg], ty: Typ, const: Boolean = true) extends Command
  case class Definition(id: Ident, args: List[Arg], ty: Option[Typ], tm: Term) extends Command
  case class Theorem(id: Ident, args: List[Arg], ty: Typ, prf: Term) extends Command

  abstract class SyntaxWriter(writer: Writer)
  {
    def write(c: Char) = writer.write(c)
    def write(s: String) = writer.write(s)

    def space = write(' ')
    def nl = write('\n')

    def bg = write('(')
    def en = write(')')

    def block(body: => Unit) { bg; body; en }
    def block_if(atomic: Boolean)(body: => Unit)
    {
      if (atomic) bg
      body
      if (atomic) en
    }

    def write(c: Command)
  }
}


// preludes for minimal Higher-order Logic (Isabelle/Pure)
// see https://raw.githubusercontent.com/Deducteam/Libraries/master/theories/stt.dk

object Prelude
{
  /* special names */

  val typeId = "Type"
  val  etaId =  "eta"
  val  epsId =  "eps"

  val TypeT = Syntax.Symb(typeId)
  val  etaT = Syntax.Symb( etaId)
  val  epsT = Syntax.Symb( epsId)


  /* kinds */

  def kind(a: String, k: Export_Theory.Kind.Value): String = a + "|" + k.toString

  def class_kind(a: String): String = kind(a, Export_Theory.Kind.CLASS)
  def type_kind(a: String): String = kind(a, Export_Theory.Kind.TYPE)
  def const_kind(a: String): String = kind(a, Export_Theory.Kind.CONST)
  def axiom_kind(a: String): String = kind(a, Export_Theory.Kind.AXIOM)
  def thm_kind(a: String): String = kind(a, Export_Theory.Kind.THM)

  def proof_kind(serial: Long): String = "proof" + serial


  val typeD = Syntax.Declaration(typeId, Nil, Syntax.TYPE)
  val  etaD = Syntax.Declaration(etaId, Nil, Syntax.arrow(TypeT, Syntax.TYPE), const = false)


  /* produces "rule f (g &a &b) → f &a ⇒ f &b */
  def rule_distr(etaeps: Syntax.Term, funimp: Syntax.Term): Syntax.Command =
  {
    val a = Syntax.BVar(0)
    val b = Syntax.BVar(1)
    val etaeps_a = Syntax.Appl(etaeps, a)
    val etaeps_b = Syntax.Appl(etaeps, b)
    Syntax.Rewrite(List("a", "b"),
      Syntax.Appl(etaeps, Syntax.appls(funimp, List(a, b))),
      Syntax.arrow(etaeps_a, etaeps_b))
  }

  val funR = rule_distr(etaT, Syntax.Symb(type_kind(Pure_Thy.FUN)))
  val impR = rule_distr(epsT, Syntax.Symb(const_kind(Pure_Thy.IMP)))

  val epsD =
  {
    val prop = Syntax.Symb(type_kind(Pure_Thy.PROP))
    val eta_prop = Syntax.Appl(etaT, prop)
    Syntax.Declaration(epsId, Nil, Syntax.arrow(eta_prop, Syntax.TYPE), const = false)
  }

  // rule eps ({|Pure.all|const|} &a &b) → ∀ (x : eta &a), eps (&b x)
  val allR =
  {
    val all = Syntax.Symb(const_kind(Pure_Thy.ALL))
    val a  = Syntax.BVar(0)
    val bl = Syntax.BVar(1)
    val br = Syntax.BVar(2)
    val eta_a = Syntax.Appl(etaT, a)
    val eps_bx = Syntax.Appl(epsT, Syntax.Appl(br, Syntax.Symb("x")))
    Syntax.Rewrite(List("a", "b"),
      Syntax.Appl(epsT, Syntax.appls(all, List(a, bl))),
      Syntax.Prod(Syntax.Arg(Some("x"), Some(eta_a)), eps_bx))
  }
}




object Translate
{
  import Prelude._

  def TypeA(name: String): Syntax.Arg =
    Syntax.Arg(Some(name), Some(TypeT))

  def TypeB(name: String)(bounds: Bounds): (Bounds, Syntax.Arg) =
    (bounds.add(name), TypeA(name))

  def etaA(name: String, ty: Term.Typ, bounds: Bounds = Bounds()) =
    Syntax.Arg(Some(name), Some(eta_ty(ty, bounds)))

  def etaB(name: String, ty: Term.Typ)(bounds: Bounds = Bounds()): (Bounds, Syntax.Arg) =
    (bounds.add(name), etaA(name, ty, bounds))

  sealed case class Bounds(
    all: List[String] = Nil,
    trm: List[String] = Nil,
    prf: List[String] = Nil) {

    def add(ty: String) =
      this.copy(all = ty :: this.all)
    def add_trm(tm: String) =
      this.copy(all = tm :: this.all, trm = tm :: this.trm)
    def add_prf(pf: String) =
      this.copy(all = pf :: this.all, prf = pf :: this.prf)

    def get(tm: String) = this.all.indexOf(tm)
    def get_trm(idx: Int) = this.all.indexOf(this.trm(idx))
    def get_prf(idx: Int) = this.all.indexOf(this.prf(idx))
  }

  def bind_args[A](
    binder: (Syntax.Arg, A) => A,
    argfuns: List[Bounds => (Bounds, Syntax.Arg)],
    rightmost: (Bounds => A),
    initial: Bounds = Bounds()): A =
    argfuns.foldRight(rightmost)((argfun, acc) => bounds => {
      val (bounds2, arg) = argfun(bounds)
      binder(arg, acc(bounds2))})(initial)

  /* types and terms */

  def typ(ty: Term.Typ, bounds: Bounds = Bounds()): Syntax.Typ =
  {
    ty match {
      case Term.TFree(a, _) =>
        bounds.get(a) match {
          case -1 => Syntax.FVar(a)
          case  i => Syntax.BVar(i)
        }
      case Term.Type(c, args) =>
        Syntax.appls(Syntax.Symb(type_kind(c)), args.map(typ(_, bounds)))
      case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
    }
  }

  def eta_ty(ty: Term.Typ, bounds: Bounds = Bounds()): Syntax.Typ =
    Syntax.Appl(etaT, typ(ty, bounds))

  def term(tm: Term.Term, bounds: Bounds): Syntax.Term =
  {
    tm match {
      case Term.Const(c, typargs) =>
        Syntax.appls(Syntax.Symb(const_kind(c)), typargs.map(typ(_, bounds)))
      case Term.Free(x, _) =>
        bounds.get(x) match {
          case -1 => Syntax.FVar(x)
          case  i => Syntax.BVar(i)
        }
      case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
      case Term.Bound(i) =>
        try Syntax.BVar(bounds.get_trm(i))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
      case Term.Abs(x, ty, b) =>
        Syntax.Abst(etaA(x, ty, bounds), term(b, bounds.add_trm(x)))
      case Term.OFCLASS(t, c) =>
        Syntax.Appl(Syntax.Symb(class_kind(c)), typ(t, bounds))
      case Term.App(a, b) =>
        Syntax.Appl(term(a, bounds), term(b, bounds))
    }
  }

  def eps_tm(tm: Term.Term, bounds: Bounds): Syntax.Term =
    Syntax.Appl(epsT, term(tm, bounds))

  def proof(prf: Term.Proof, bounds: Bounds): Syntax.Term =
  {
    prf match {
      case Term.PBound(i) =>
        try Syntax.BVar(bounds.get_prf(i))
        catch {
          case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i)
        }
      case Term.Abst(x, ty, b) =>
        Syntax.Abst(etaA(x, ty, bounds), proof(b, bounds.add_trm(x)))
      case Term.AbsP(x, hy, b) =>
        Syntax.Abst(
          Syntax.Arg(Some(x), Some (eps_tm(hy, bounds))),
          proof(b, bounds.add_prf(x)))
      case Term.Appt(a, b) =>
        Syntax.Appl(proof(a, bounds), term(b, bounds))
      case Term.AppP(a, b) =>
        Syntax.Appl(proof(a, bounds), proof(b, bounds))
      case axm: Term.PAxm =>
        Syntax.appls(Syntax.Symb(axiom_kind(axm.name)), axm.types.map(typ(_, bounds)))
      case thm: Term.PThm =>
        val head = if (thm.name.nonEmpty) thm_kind(thm.name) else proof_kind(thm.serial)
        Syntax.appls(Syntax.Symb(head), thm.types.map(typ(_, bounds)))
      case _ => error("Bad proof term encountered:\n" + prf)
    }
  }


  /* type classes */

  def class_decl(c: String): Syntax.Command =
  {
    val eta_prop = Syntax.Appl(etaT, Syntax.Symb(type_kind(Pure_Thy.PROP)))
    Syntax.Declaration(class_kind(c), Nil, Syntax.arrow(TypeT, eta_prop))
  }


  /* types */

  def type_decl(c: String, args: Int): Syntax.Command =
    Syntax.Declaration(type_kind(c), Nil,
      Syntax.arrows(List.fill(args)(TypeT), TypeT))

  def type_abbrev(c: String, args: List[String], rhs: Term.Typ): Syntax.Command =
    Syntax.Definition(type_kind(c), args.map(TypeA), Some(TypeT), typ(rhs))


  /* consts */

  def const_decl(c: String, typargs: List[String], ty: Term.Typ): Syntax.Command =
    Syntax.Declaration(const_kind(c), Nil,
      bind_args(Syntax.Prod, typargs.map(TypeB), eta_ty(ty, _)))

  def const_abbrev(c: String, typargs: List[String], ty: Term.Typ, rhs: Term.Term): Syntax.Command =
    Syntax.Definition(const_kind(c), typargs.map(TypeA),
      Some(eta_ty(ty)), term(rhs, Bounds()))


  /* theorems and proof terms */

  def stmt_decl(
    s: String,
    prop: Export_Theory.Prop,
    proof_term: Option[Term.Proof]): Syntax.Command =
  {
    val argfuns: List[Bounds => (Bounds, Syntax.Arg)] =
      prop.typargs.map(_._1).map(TypeB) ++
      prop.args.map((etaB _).tupled)
    val ty = bind_args(Syntax.Prod, argfuns, eps_tm(prop.term, _))

    try proof_term match {
      case None => Syntax.Declaration(s, Nil, ty)
      case Some(prf) =>
        Syntax.Theorem(s, Nil, ty, bind_args(Syntax.Abst, argfuns, proof(prf, _)))
    }
    catch { case ERROR(msg) => error(msg + "\nin " + quote(s)) }
  }

  def proof_decl(serial: Long, prop: Export_Theory.Prop, prf: Term.Proof): Syntax.Command =
    stmt_decl(Prelude.proof_kind(serial), prop, Some(prf))

}


class PartWriter(file: Path) extends Writer
{
  private val file_part = file.ext("part")

  private val w =
    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file_part.file), UTF8.charset))

  def write(c: Char) = w.write(c)
  def write(a: Array[Char], off: Int, len: Int) = w.write(a, off, len)
  def flush() = w.flush()

  def close()
  {
    w.close()
    File.move(file_part, file)
  }
}


object LP_Syntax
{
  /* reserved */

  val reserved =
    Set(
      "require",
      "open",
      "as",
      "let",
      "in",
      "symbol",
      "definition",
      "theorem",
      "rule",
      "and",
      "assert",
      "assertnot",
      "const",
      "injective",
      "TYPE",
      "pos",
      "neg",
      "proof",
      "refine",
      "intro",
      "apply",
      "simpl",
      "rewrite",
      "reflexivity",
      "symmetry",
      "focus",
      "print",
      "proofterm",
      "qed",
      "admit",
      "abort",
      "set",
      "_",
      "type",
      "compute")


  /* names */

  def is_regular_identifier(name: String): Boolean =
    name.nonEmpty &&
    { val c = name(0); Symbol.is_ascii_letter(c) || c == '_' } &&
    name.forall(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_')

  def make_escaped_identifier(name: String): String =
    if (name.containsSlice("|}")) error("Bad name: " + quote(name))
    else "{|" + name + "|}"

  def escape_if_needed(a: String) : String =
    if (reserved(a) || !is_regular_identifier(a)) make_escaped_identifier(a) else a


  class SyntaxWriter(writer: Writer) extends Syntax.SyntaxWriter(writer)
  {
    def name(a: String): Unit = write(escape_if_needed(a))

    def comma  = write(", ")
    def colon  = write(" : ")
    def to     = write(" \u21d2 ")
    def rew    = write(" \u2192 ")
    def dfn    = write(" \u2254 ")
    def lambda = write("\u03bb ")
    def forall = write("\u2200 ")

    def arg(a: Syntax.Arg, bounds: List[String] = Nil)
    {
      a.id match {
        case Some(id) => name(id)
        case None => write('_')
      }
      for (t <- a.typ) { colon; term(t, bounds) }
    }

    def bind(arg: Syntax.Arg, bounds: List[String]) =
    {
      arg match {
        case Syntax.Arg(Some(name), _) => escape_if_needed(name) :: bounds
        case _ => bounds
      }
    }

    def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false)
    {
      t match
      {
        case Syntax.TYPE =>
          write("TYPE")
        case Syntax.Symb(id) =>
          name(id)
        case Syntax.FVar(id) =>
          assert(!bounds.contains(escape_if_needed(id)))
          name(id)
        case Syntax.BVar(idx) =>
          write(bounds(idx))
        case Syntax.Appl(t1, t2) =>
          block_if(atomic) {
            term(t1, bounds, atomic = true)
            space
            term(t2, bounds, atomic = true)
          }
        case Syntax.Abst(a, t) =>
          block_if(atomic) { lambda; block { arg(a, bounds) }; comma; term(t, bind(a, bounds)) }
        case Syntax.Prod(a, t) =>
          block_if(atomic) { forall; block { arg(a, bounds) }; comma; term(t, bind(a, bounds)) }
      }
    }

    def write(c: Syntax.Command)
    {
      c match
      {
        case Syntax.Rewrite(vars, lhs, rhs) =>
          val ampvars = vars.map(v => "&" ++ v)
          write("rule ")
          term(lhs, ampvars)
          rew
          term(rhs, ampvars)
        case Syntax.Declaration(id, args, ty, const) =>
          write("symbol ")
          if (const) write("const ")
          name(id)
          for (a <- args) { space; block { arg(a) } }
          colon
          term(ty)
        case Syntax.Definition(id, args, ty, tm) =>
          write("definition ");
          name(id)
          for (a <- args) { space; block { arg(a) } }
          for (ty <- ty) { colon; term(ty) }
          dfn
          term(tm)
        case Syntax.Theorem(id, args, ty, prf) =>
          write("theorem ");
          name(id)
          for (a <- args) { space; block { arg(a) } }
          colon; term(ty)
          write(" proof refine ")
          term(prf)
          write(" qed")
      }
      nl
    }

    def require_open(module: String) =
    {
      write("require open ")
      name(module)
      nl
    }
  }
}
