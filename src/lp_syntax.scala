/** Dedukti lp syntax **/
// see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf

package isabelle.dedukti


import isabelle._


object LP_Syntax
{
  // FIXME move to term.scala / logic.scala in Isabelle (!?)
  object Logic
  {
    /* types */

    def aT(s: Term.Sort): Term.Typ = Term.TFree("'a", s)
    def itselfT(ty: Term.Typ): Term.Typ = Term.Type(Pure_Thy.ITSELF, List(ty))
    val propT: Term.Typ = Term.Type(Pure_Thy.PROP, Nil)
    def funT(ty1: Term.Typ, ty2: Term.Typ): Term.Typ = Term.Type(Pure_Thy.FUN, List(ty1, ty2))

    def add_tfreesT(ty: Term.Typ, res: List[(String, Term.Sort)]): List[(String, Term.Sort)] =
    {
      ty match {
        case Term.Type(_, tys) => (res /: tys) { case (r, t) => add_tfreesT(t, r) }
        case Term.TFree(a, s) => Library.insert((a, s))(res)
        case _ => res
      }
    }

    def add_tfrees(tm: Term.Term, res: List[(String, Term.Sort)]): List[(String, Term.Sort)] =
    {
      tm match {
        case Term.Const(_, ty) => add_tfreesT(ty, res)
        case Term.Free(_, ty) => add_tfreesT(ty, res)
        case Term.Var(_, ty) => add_tfreesT(ty, res)
        case Term.Bound(_) => res
        case Term.Abs(_, ty, b) => add_tfrees(b, add_tfreesT(ty, res))
        case Term.App(a, b) => add_tfrees(b, add_tfrees(a, res))
      }
    }


    /* type as term (polymorphic unit) */

    def mk_type(ty: Term.Typ): Term.Term = Term.Const("Pure.type", itselfT(ty))


    /* type classes (within the logic) */

    def const_of_class(c: String): String = c + "_class"

    def mk_of_class(ty: Term.Typ, c: String): Term.Term =
      Term.App(Term.Const(const_of_class(c), funT(itselfT(ty), propT)), mk_type(ty))

    def mk_of_sort(ty: Term.Typ, s: Term.Sort): List[Term.Term] =
      s.map(c => mk_of_class(ty, c))

    def mk_classrel(c1: String, c2: String): Term.Term =
      mk_of_class(aT(List(c1)), c2)

    def mk_arity(a: String, sorts: List[Term.Sort], c: String): Term.Term =
    {
      val names =
        sorts.length match {
          case 0 => Nil
          case 1 => List("'a")
          case 2 => List("'a", "'b")
          case 3 => List("'a", "'b", "'c")
          case n => (1 to n).toList.map(i => "'a" + i)
        }
      val ty = Term.Type(a, for ((name, sort) <- names zip sorts) yield Term.TFree(name, sort))
      mk_of_class(ty, c)
    }
  }


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


  /* kinds */

  def append_kind(a: String, kind: String): String =
    if (kind.isEmpty) a else a + "|" + kind

  def kind_type(a: String): String = append_kind(a, Export_Theory.Kind.TYPE.toString)
  def kind_const(a: String): String = append_kind(a, Export_Theory.Kind.CONST.toString)
  def kind_fact(a: String): String = append_kind(a, Export_Theory.Kind.FACT.toString)


  /* buffered output depending on context (unsynchronized) */

  sealed case class Type_Scheme(typargs: List[String], template: Term.Typ)
  {
    def match_typargs(c: String, typ: Term.Typ): List[Term.Typ] =
      Term.const_typargs(c, typ, typargs, template)
  }

  class Output
  {
    /* logical context */

    var context_type_scheme: Map[String, Type_Scheme] = Map.empty

    def match_typargs(c: String, typ: Term.Typ): List[Term.Typ] =
    {
      context_type_scheme.getOrElse(c, error("Undefined type_scheme for " + quote(c)))
        .match_typargs(c, typ)
    }

    def declare_type_scheme(c: String, typargs: List[String], template: Term.Typ)
    {
      if (context_type_scheme.isDefinedAt(c)) {
        error("Duplicate declaration of type scheme for " + quote(c))
      }
      else context_type_scheme += (c -> Type_Scheme(typargs, template))
    }


    /* text buffer */

    val buffer = new StringBuilder
    def write(path: Path) = File.write(path, buffer.toString)

    def char(c: Char): Unit = buffer += c
    def string(s: String): Unit = buffer ++= s


    /* white space */

    def space: Unit = char(' ')
    def nl: Unit = char('\n')


    /* blocks (parentheses) */

    def bg { string("(") }
    def en { string(")") }

    def block(body: => Unit) { bg; body; en }
    def block_if(atomic: Boolean)(body: => Unit)
    {
      if (atomic) bg
      body
      if (atomic) en
    }


    /* concrete syntax and special names */

    def comma { string(", ") }
    def symbol_const { string("symbol const ") }
    def symbol { string("symbol ") }
    def definition { string("definition ") }
    def rule { string("rule ") }
    def TYPE { string("TYPE") }
    def Type { string("Type") }
    def eta { string("eta") }
    def eps { string("eps") }
    def colon { string(" : ") }
    def to { string(" \u21d2 ") }
    def dfn { string(" \u2254 ") }
    def rew { string(" \u2192 ") }
    def all { string("\u2200 ") }
    def lambda { string("\u03bb ") }


    /* names */

    def name(a: String): Unit =
      string(if (reserved(a) || !is_regular_identifier(a)) make_escaped_identifier(a) else a)


    /* types and terms */

    def typ(ty: Term.Typ, atomic: Boolean = false)
    {
      ty match {
        case Term.TFree(a, _) => name(a)
        case Term.Type(c, Nil) => name(kind_type(c))
        case Term.Type(c, args) =>
          block_if(atomic) {
            name(kind_type(c))
            for (arg <- args) {
              space
              typ(arg, atomic = true)
            }
          }
        case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
      }
    }

    def eta_typ(ty: Term.Typ, atomic: Boolean = false)
    {
      block_if(atomic) { eta; space; typ(ty, atomic = true) }
    }

    def term(tm: Term.Term, bounds: List[String] = Nil, atomic: Boolean = false)
    {
      tm match {
        case Term.Const(c, ty) =>
          val types = match_typargs(kind_const(c), ty)
          block_if(atomic && types.nonEmpty) {
            name(kind_const(c))
            for (t <- types) { space; typ(t, atomic = true) }
          }
        case Term.Free(x, _) => name(x)
        case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
        case Term.Bound(i) =>
          val x =
            try { bounds(i) }
            catch {
              case _: IndexOutOfBoundsException =>
                isabelle.error("Loose de-Bruijn index " + i)
            }
          name(x)
        case Term.Abs(x, ty, b) =>
          block_if(atomic) {
            lambda; block { name(x); colon; eta_typ(ty) }; comma
            term(b, bounds = x :: bounds)
          }
        case Term.App(a, b) =>
          block_if(atomic) {
            term(a, bounds = bounds, atomic = true)
            space
            term(b, bounds = bounds, atomic = true)
          }
      }
    }

    def eps_term(t: Term.Term, atomic: Boolean = false)
    {
      block_if(atomic) { eps; space; term(t, atomic = true) }
    }


    /* types */

    def type_decl(c: String, args: Int)
    {
      symbol_const; name(kind_type(c)); colon
      for (_ <- 0 until args) { Type; to }; Type
      nl
    }

    def type_abbrev(c: String, args: List[String], rhs: Term.Typ)
    {
      definition; name(kind_type(c))
      for (a <- args) { space; block { name(a); colon; Type } }
      colon; Type; dfn; typ(rhs)
      nl
    }


    def polymorphic(typargs: List[String])
    {
      if (typargs.nonEmpty) {
        all; for (a <- typargs) { block { name(a); colon; Type }; space }; comma
      }
    }


    /* consts */

    def const_decl(c: String, typargs: List[String], ty: Term.Typ)
    {
      declare_type_scheme(kind_const(c), typargs, ty)
      symbol_const; name(kind_const(c)); colon; polymorphic(typargs); eta_typ(ty)
      nl
    }

    def const_abbrev(c: String, typargs: List[String], ty: Term.Typ, rhs: Term.Term)
    {
      declare_type_scheme(kind_const(c), typargs, ty)
      definition; name(kind_const(c))
      for (a <- typargs) { space; block { name(a); colon; Type } }
      colon; eta_typ(ty); dfn; term(rhs)
      nl
    }


    /* facts */

    def fact_decl(c: String, prop: Export_Theory.Prop)
    {
      symbol_const; name(kind_fact(c)); colon
      polymorphic(prop.typargs.map(_._1))
      for ((a, s) <- prop.typargs; of_class <- Logic.mk_of_sort(Term.TFree(a, Nil), s)) {
        eps_term(of_class); to
      }
      if (prop.args.nonEmpty) {
        all; for ((x, ty) <- prop.args) { block { name(x); colon; eta_typ(ty) }; space }; comma
      }
      eps_term(prop.term)
      nl
    }


    /* sort algebra */

    var classrel_count = 0
    var arity_count = 0

    def classrel(c1: String, c2: String)
    {
      classrel_count += 1

      val t = Logic.mk_classrel(c1, c2)
      val typargs = Logic.add_tfrees(t, Nil).reverse
      fact_decl("classrel_" + classrel_count, Export_Theory.Prop(typargs, Nil, t))
    }

    def arity(a: String, sorts: List[Term.Sort], c: String)
    {
      arity_count += 1

      val t = Logic.mk_arity(a, sorts, c)
      val typargs = Logic.add_tfrees(t, Nil).reverse
      fact_decl("arity_" + arity_count, Export_Theory.Prop(typargs, Nil, t))
    }
    

    /* preludes for minimal Higher-order Logic (Isabelle/Pure) */
    // see https://raw.githubusercontent.com/Deducteam/Libraries/master/theories/stt.dk

    def prelude_type
    {
      symbol_const; Type; colon; TYPE; nl
      symbol; eta; colon; Type; to; TYPE; nl
    }

    def prelude_fun
    {
      rule; eta; space; block { name(kind_type(Pure_Thy.FUN)); string(" &a &b") }; rew;
        eta; string(" &a"); to; eta; string(" &b"); nl
    }

    def prelude_prop
    {
      symbol; eps; colon; eta; space; name(kind_type(Pure_Thy.PROP)); to; TYPE; nl
    }

    def prelude_all
    {
      rule; eps; space; block { name(kind_const(Pure_Thy.ALL)); string(" &a &b") }; rew;
        all; block { string("x"); colon; eta; string(" &a") }; comma; eps; string(" (&b x)"); nl
    }

    def prelude_imp
    {
      rule; eps; space; block { name(kind_const(Pure_Thy.IMP)); string(" &a &b") }; rew;
        eps; string(" &a"); to; eps; string(" &b"); nl
    }
  }
}
