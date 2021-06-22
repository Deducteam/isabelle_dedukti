/** Translation of Isabelle (proof)terms into lambda-Pi calculus **/


package isabelle.dedukti

import isabelle.Export_Theory.{No_Syntax, Prefix}
import isabelle._


// preludes for minimal Higher-order Logic (Isabelle/Pure)
// see https://raw.githubusercontent.com/Deducteam/Libraries/master/theories/stt.dk

object Prelude
{
  /* kinds */

  def kind(a: String, k: String): String = k + "_" + a.replace('.', '+') // a + "|" + k

  def class_kind(a: String): String = kind(a, Markup.CLASS)
  def type_kind (a: String): String = kind(a, Export_Theory.Kind.TYPE)
  def const_kind(a: String): String = kind(a, Export_Theory.Kind.CONST)
  def axiom_kind(a: String): String = kind(a, Markup.AXIOM)
  def thm_kind  (a: String): String = kind(a, Export_Theory.Kind.THM)

  def proof_kind(serial: Long): String = "proof" + serial

  /* special names */

  val typeId = "Typ"
  val  etaId = "eta"
  val  epsId = "eps"

  val TypeT: Syntax.Term = Syntax.Symb(typeId)
  val  etaT: Syntax.Term = Syntax.Symb( etaId)
  val  epsT: Syntax.Term = Syntax.Symb( epsId)


  val typeD: Syntax.Command  = Syntax.Declaration(typeId, Nil, Syntax.TYPE, not = None)
  val  etaN: Syntax.Notation = Syntax.Prefix("η", 10)
  val  etaD: Syntax.Command  = Syntax.DefableDecl(etaId, Syntax.arrow(TypeT, Syntax.TYPE), not = Some(etaN))




  val epsN: Syntax.Notation = Syntax.Prefix("ε", 10)
  val epsD: Syntax.Command =
  {
    val prop = Syntax.Symb(type_kind(Pure_Thy.PROP))
    val eta_prop = Syntax.Appl(etaT, prop)
    Syntax.DefableDecl(epsId, Syntax.arrow(eta_prop, Syntax.TYPE), not = Some(epsN))
  }

  // Integration rewrites

  /* produces "rule f (g &a &b) → f &a ⇒ f &b */
  def rule_distr(etaeps: Syntax.Term, funimp: Syntax.Term): Syntax.Command =
  {
    val a = Syntax.Var("a")
    val b = Syntax.Var("b")
    val etaeps_a = Syntax.Appl(etaeps, a)
    val etaeps_b = Syntax.Appl(etaeps, b)
    Syntax.Rewrite(List("a", "b"),
      Syntax.Appl(etaeps, Syntax.appls(funimp, List(a, b))),
      Syntax.arrow(etaeps_a, etaeps_b))
  }

  val funR: Syntax.Command = rule_distr(etaT, Syntax.Symb(type_kind(Pure_Thy.FUN)))
  val impR: Syntax.Command = rule_distr(epsT, Syntax.Symb(const_kind(Pure_Thy.IMP)))

  // rule eps ({|Pure.all|const|} &a &b) → ∀ (x : eta &a), eps (&b x)
  val allR: Syntax.Command =
  {
    val all = Syntax.Symb(const_kind(Pure_Thy.ALL))
    val a = Syntax.Var("a")
    val b = Syntax.Var("b")
    val lhs = Syntax.Appl(epsT, Syntax.Appl(Syntax.Appl(all, a, isImplicit = true), b))
    val eta_a = Syntax.Appl(etaT, a)
    val eps_bx = Syntax.Appl(epsT, Syntax.Appl(b, Syntax.Var("x")))
    Syntax.Rewrite(List("a", "b"),
      lhs,
      Syntax.Prod(Syntax.BoundArg(Some("x"), Some(eta_a)), eps_bx))
  }
}



object Translate
{
  import Prelude._

  def bound_type_argument(name: String, impl: Boolean = false): Syntax.BoundArg =
    Syntax.BoundArg(Some(name), Some(TypeT), impl)

  def bound_argument(name: String, ty: Term.Typ): Syntax.BoundArg =
    Syntax.BoundArg(Some(name), Some(eta_ty(ty)))

  sealed case class Bounds(
    trm: List[String] = Nil,
    prf: List[String] = Nil)
  {
    def add_trm(tm: String): Bounds = copy(trm = tm :: trm)
    def add_prf(pf: String): Bounds = copy(prf = pf :: prf)

    def get_trm(idx: Int): String = trm(idx)
    def get_prf(idx: Int): String = prf(idx)
  }

  /* types and terms */

  def typ(ty: Term.Typ): Syntax.Typ =
  {
    ty match {
      case Term.TFree(a, _) =>
        Syntax.Var(a)
      case Term.Type(c, args) =>
        Syntax.appls(Syntax.Symb(type_kind(c)), args.map(typ))
      case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
    }
  }

  def eta_ty(ty: Term.Typ): Syntax.Typ =
    Syntax.Appl(etaT, typ(ty))

  def term(tm: Term.Term, bounds: Bounds): Syntax.Term =
  {
    tm match {
      case Term.Const(c, typargs) =>
        Syntax.appls(Syntax.Symb(const_kind(c)), typargs.map(typ), impl = true)
      case Term.Free(x, _) =>
        Syntax.Var(x)
      case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
      case Term.Bound(i) =>
        try Syntax.Var(bounds.get_trm(i))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
      case Term.Abs(x, ty, b) =>
        Syntax.Abst(bound_argument(x, ty), term(b, bounds.add_trm(x)))
      case Term.OFCLASS(t, c) =>
        Syntax.Appl(Syntax.Symb(class_kind(c)), typ(t))
      case Term.App(a, b) =>
        Syntax.Appl(term(a, bounds), term(b, bounds))
    }
  }

  def eps_tm(tm: Term.Term, bounds: Bounds): Syntax.Term =
    Syntax.Appl(epsT, term(tm, bounds))

  def proof(prf: Term.Proof, bounds: Bounds): Syntax.Term = {
    prf match {
      case Term.PBound(i) =>
        try Syntax.Var(bounds.get_prf(i))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i) }
      case Term.Abst(x, ty, b) =>
        Syntax.Abst(bound_argument(x, ty), proof(b, bounds.add_trm(x)))
      case Term.AbsP(x, hy, b) =>
        Syntax.Abst(
          Syntax.BoundArg(Some(x), Some (eps_tm(hy, bounds))),
          proof(b, bounds.add_prf(x)))
      case Term.Appt(a, b) =>
        Syntax.Appl(proof(a, bounds), term(b, bounds))
      case Term.AppP(a, b) =>
        Syntax.Appl(proof(a, bounds), proof(b, bounds))
      case axm: Term.PAxm =>
        Syntax.appls(Syntax.Symb(axiom_kind(axm.name)), axm.types.map(typ))
      case thm: Term.PThm =>
        val head = if (thm.name.nonEmpty) thm_kind(thm.name) else proof_kind(thm.serial)
        Syntax.appls(Syntax.Symb(head), thm.types.map(typ))
      case _ => error("Bad proof term encountered:\n" + prf)
    }
  }

  /* notation */

  val notationDict = Map(
    "_" -> "__",
    "\\<Rightarrow>" -> "⇒",
    "\\<equiv>" -> "⩵",
    "\\<Longrightarrow>" -> "⟹",
    "\\<And>" -> "⋀",
    "\\<longrightarrow>" -> "⟶"
  )

  def notation_decl: Export_Theory.Syntax => Option[Syntax.Notation] = { // TODO: Ugly
    case No_Syntax => None
    case Prefix(op) => Some(Syntax.Prefix(notationDict getOrElse(op, op), Syntax.defaultPrefixPriority))
    case Export_Theory.Infix(Export_Theory.Assoc.NO_ASSOC,    op, priority) => Some(Syntax.Infix (notationDict getOrElse(op, op), priority + 1))
    case Export_Theory.Infix(Export_Theory.Assoc.LEFT_ASSOC,  op, priority) => Some(Syntax.InfixL(notationDict getOrElse(op, op), priority + 1))
    case Export_Theory.Infix(Export_Theory.Assoc.RIGHT_ASSOC, op, priority) => Some(Syntax.InfixR(notationDict getOrElse(op, op), priority + 1))
  }


  /* type classes */

  def class_decl(c: String): Syntax.Command = {
    val eta_prop = Syntax.Appl(etaT, Syntax.Symb(type_kind(Pure_Thy.PROP)))
    Syntax.Declaration(class_kind(c), Nil, Syntax.arrow(TypeT, eta_prop))
  }


  /* types */

  def type_decl(c: String, args: List[String], rhs: Option[Term.Typ], not: Export_Theory.Syntax): Syntax.Command =
    rhs match {
      case None =>
        Syntax.Declaration(type_kind(c), Nil,
          Syntax.arrows(List.fill(args.length)(TypeT), TypeT),
          notation_decl(not)
        )
      case Some(rhs) =>
        Syntax.Definition(type_kind(c), args.map(bound_type_argument(_)), Some(TypeT), typ(rhs), notation_decl(not))
    }


  /* consts */

  def const_decl(c: String, typargs: List[String], ty: Term.Typ, rhs: Option[Term.Term], not: Export_Theory.Syntax): Syntax.Command =
    rhs match {
      case None =>
        Syntax.Declaration(const_kind(c), typargs.map(bound_type_argument(_, impl = true)), eta_ty(ty), notation_decl(not))
      case Some(rhs) =>
        Syntax.Definition (const_kind(c), typargs.map(bound_type_argument(_, impl = true)),
          Some(eta_ty(ty)), term(rhs, Bounds()), notation_decl(not))
    }


  /* theorems and proof terms */

  def stmt_decl(s: String, prop: Export_Theory.Prop, prf_opt: Option[Term.Proof]): Syntax.Command = {
    val args =
      prop.typargs.map(_._1).map(bound_type_argument(_)) :::
      prop.args.map(arg => bound_argument(arg._1, arg._2))
    val ty = eps_tm(prop.term, Bounds())

    try prf_opt match {
      case None => Syntax.Declaration(s, args, ty)
      case Some(prf) =>
        Syntax.Theorem(s, args, ty, proof(prf, Bounds()))
    }
    catch { case ERROR(msg) => error(msg + "\nin " + quote(s)) }
  }
}
