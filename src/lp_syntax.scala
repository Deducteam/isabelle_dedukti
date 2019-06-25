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
          if (atomic) string("(")
          name(c)
          for (arg <- args) {
            space
            typ(arg, atomic = true)
          }
          if (atomic) string(")")
        case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
      }
    }


    /* concrete syntax and special names */

    def symbol_const: Unit = string("symbol const ")
    def definition: Unit = string("definition ")
    def TYPE: Unit = string("TYPE")
    def Type: Unit = string("Type")
    def eta: Unit = string("eta")
    def colon: Unit = string(" : ")
    def to: Unit = string(" \u21d2 ")
    def dfn: Unit = string(" \u2254 ")


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


    /* prelude */

    symbol_const; Type; colon; TYPE; nl
    symbol_const; eta; colon; Type; to; TYPE; nl
    nl
  }
}
