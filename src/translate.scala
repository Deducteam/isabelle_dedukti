/** Translation of Isabelle (proof)terms into lambda-Pi calculus **/


package isabelle.dedukti

import isabelle._


// preludes for minimal Higher-order Logic (Isabelle/Pure)
// see https://raw.githubusercontent.com/Deducteam/Libraries/master/theories/stt.dk

object Prelude
{
  /* special names */

  val typeId = "Typ"
  val  etaId = "eta"
  val  epsId = "eps"

  val TypeT = Syntax.Symb(typeId)
  val  etaT = Syntax.Symb( etaId)
  val  epsT = Syntax.Symb( epsId)


  /* kinds */

  def kind(a: String, k: String): String = a + "|" + k

  def class_kind(a: String): String = kind(a, Markup.CLASS)
  def type_kind(a: String): String = kind(a, Export_Theory.Kind.TYPE)
  def const_kind(a: String): String = kind(a, Export_Theory.Kind.CONST)
  def axiom_kind(a: String): String = kind(a, Markup.AXIOM)
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

  val funR: Syntax.Command = rule_distr(etaT, Syntax.Symb(type_kind(Pure_Thy.FUN)))
  val impR: Syntax.Command = rule_distr(epsT, Syntax.Symb(const_kind(Pure_Thy.IMP)))

  val epsD: Syntax.Declaration =
  {
    val prop = Syntax.Symb(type_kind(Pure_Thy.PROP))
    val eta_prop = Syntax.Appl(etaT, prop)
    Syntax.Declaration(epsId, Nil, Syntax.arrow(eta_prop, Syntax.TYPE), const = false)
  }

  // rule eps ({|Pure.all|const|} &a &b) → ∀ (x : eta &a), eps (&b x)
  val allR: Syntax.Rewrite =
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

  def etaA(name: String, ty: Term.Typ, bounds: Bounds = Bounds()): Syntax.Arg =
    Syntax.Arg(Some(name), Some(eta_ty(ty, bounds)))

  def etaB(name: String, ty: Term.Typ)(bounds: Bounds = Bounds()): (Bounds, Syntax.Arg) =
    (bounds.add(name), etaA(name, ty, bounds))

  sealed case class Bounds(
    all: List[String] = Nil,
    trm: List[String] = Nil,
    prf: List[String] = Nil)
  {
    def add(ty: String): Bounds = copy(all = ty :: all)
    def add_trm(tm: String): Bounds = copy(all = tm :: all, trm = tm :: trm)
    def add_prf(pf: String): Bounds = copy(all = pf :: all, prf = pf :: prf)

    def get(tm: String): Int = all.indexOf(tm)
    def get_trm(idx: Int): Int = all.indexOf(trm(idx))
    def get_prf(idx: Int): Int = all.indexOf(prf(idx))
  }

  def bind_args[A](
    binder: (Syntax.Arg, A) => A,
    argfuns: List[Bounds => (Bounds, Syntax.Arg)],
    rightmost: (Bounds => A),
    initial: Bounds = Bounds()): A =
    argfuns.foldRight(rightmost)((argfun, acc) => bounds =>
    {
      val (bounds2, arg) = argfun(bounds)
      binder(arg, acc(bounds2))
    })(initial)

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

  def type_decl(c: String, args: List[String], rhs: Option[Term.Typ]): Syntax.Command =
    rhs match {
      case None =>
        Syntax.Declaration(type_kind(c), Nil,
          Syntax.arrows(List.fill(args.length)(TypeT), TypeT))
      case Some(rhs) =>
        Syntax.Definition(type_kind(c), args.map(TypeA), Some(TypeT), typ(rhs))
    }


  /* consts */

  def const_decl(c: String, typargs: List[String], ty: Term.Typ, rhs: Option[Term.Term]): Syntax.Command =
    rhs match {
      case None =>
        Syntax.Declaration(const_kind(c), Nil,
          bind_args(Syntax.Prod, typargs.map(TypeB), eta_ty(ty, _)))
      case Some(rhs) =>
        Syntax.Definition(const_kind(c), typargs.map(TypeA),
          Some(eta_ty(ty)), term(rhs, Bounds()))
    }


  /* theorems and proof terms */

  def stmt_decl(
    s: String,
    prop: Export_Theory.Prop,
    proof_term: Option[Term.Proof]): Syntax.Command =
  {
    val argfuns: List[Bounds => (Bounds, Syntax.Arg)] =
      prop.typargs.map(_._1).map(TypeB) :::
      prop.args.map((etaB _).tupled)
    val ty = bind_args(Syntax.Prod, argfuns, eps_tm(prop.term, _))

    try proof_term match {
      case None => Syntax.Declaration(s, Nil, ty)
      case Some(prf) =>
        Syntax.Theorem(s, Nil, ty, bind_args(Syntax.Abst, argfuns, proof(prf, _)))
    }
    catch { case ERROR(msg) => error(msg + "\nin " + quote(s)) }
  }
}
