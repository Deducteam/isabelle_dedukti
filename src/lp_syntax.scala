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


  /* buffered output (unsynchronized) */

  class Output
  {
    val buffer = new StringBuilder
    def write(path: Path) = File.write(path, buffer.toString)

    def char(c: Char): Unit = buffer += c
    def string(s: String): Unit = buffer ++= s


    /* white space */

    def space: Unit = char(' ')
    def nl: Unit = char('\n')


    /* names */

    def name(a: String): Unit =
      string(if (reserved(a) || !is_regular_identifier(a)) make_escaped_identifier(a) else a)


    /* types and terms */

    def typ(ty: Term.Typ, atomic: Boolean = false)
    {
      ty match {
        case Term.TFree(a, _) => name(a)
        case Term.Type(c, Nil) => name(c)
        case Term.Type(c, args) =>
          if (atomic) bg
          name(c)
          for (arg <- args) {
            space
            typ(arg, atomic = true)
          }
          if (atomic) en
        case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
      }
    }


    /* concrete syntax and special names */

    def bg { string("(") }
    def en { string(")") }
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


    /* type declarations */

    def type_decl(c: String, args: Int)
    {
      symbol_const; name(c); colon
      for (_ <- 0 until args) { Type; to }; Type
      nl
    }

    def type_abbrev(c: String, args: List[String], rhs: Term.Typ)
    {
      definition; name(c);
      for (a <- args) { space; name(a) }
      colon; Type; dfn; typ(rhs)
      nl
    }


    /* preludes for minimal Higher-order Logic (Isabelle/Pure) */
    // see https://raw.githubusercontent.com/Deducteam/Libraries/master/theories/stt.dk

    def prelude_type
    {
      symbol_const; Type; colon; TYPE; nl
      symbol; eta; colon; Type; to; TYPE; nl
      nl
    }

    def prelude_fun
    {
      rule; eta; space; bg; name(Pure_Thy.FUN); string(" &a &b"); en; rew;
        eta; string(" &a"); to; eta; string(" &b"); nl
    }

    def prelude_prop
    {
      symbol; eps; colon; eta; space; name(Pure_Thy.PROP); to; TYPE; nl
    }

    def prelude_all
    {
      rule; eps; space; bg; name(Pure_Thy.ALL); string(" &a &b"); en; rew;
        all; bg; string("x"); colon; eta; string(" &a"); en; comma; eps; string(" (&b x)"); nl
    }

    def prelude_imp
    {
      rule; eps; space; bg; name(Pure_Thy.IMP); string(" &a &b"); en; rew;
        eps; string(" &a"); to; eps; string(" &b"); nl
    }
  }
}
