/** Dedukti lp syntax **/
// see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf

package isabelle.dedukti


import isabelle._


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
      for ((a, s) <- prop.typargs; of_class <- Term.mk_of_sort(Term.TFree(a, Nil), s)) {
        eps_term(of_class); to
      }
      if (prop.args.nonEmpty) {
        all; for ((x, ty) <- prop.args) { block { name(x); colon; eta_typ(ty) }; space }; comma
      }
      eps_term(prop.term)
      nl
    }


    /* sort algebra */

    var sort_algebra_count = 0

    def sort_algebra(prop: Export_Theory.Prop)
    {
      sort_algebra_count += 1
      fact_decl("sort_algebra_" + sort_algebra_count, prop)
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
