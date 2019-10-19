/** Dedukti lp syntax **/
// see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf

package isabelle.dedukti


import isabelle._

import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter}


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

  def kind(a: String, k: Export_Theory.Kind.Value): String = a + "|" + k.toString

  def class_kind(a: String): String = kind(a, Export_Theory.Kind.CLASS)
  def type_kind(a: String): String = kind(a, Export_Theory.Kind.TYPE)
  def const_kind(a: String): String = kind(a, Export_Theory.Kind.CONST)
  def axiom_kind(a: String): String = kind(a, Export_Theory.Kind.AXIOM)
  def proof_kind(serial: Long): String = kind(serial.toString, Export_Theory.Kind.PROOF)


  /* buffered output depending on context (unsynchronized) */

  class Output(file: Path) extends AutoCloseable
  {
    /* manage output file */

    private val file_part = file.ext("part")

    private val writer =
      new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file_part.file), UTF8.charset))

    def char(c: Char): Unit = writer.write(c)
    def string(s: String): Unit = writer.write(s)

    def close()
    {
      writer.close
      File.move(file_part, file)
    }


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
        case Term.Type(c, Nil) => name(type_kind(c))
        case Term.Type(c, args) =>
          block_if(atomic) {
            name(type_kind(c))
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
        case Term.Const(c, typargs) =>
          block_if(atomic && typargs.nonEmpty) {
            name(const_kind(c))
            for (t <- typargs) { space; typ(t, atomic = true) }
          }
        case Term.Free(x, _) => name(x)
        case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
        case Term.Bound(i) =>
          try { name(bounds(i)) }
          catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
        case Term.Abs(x, ty, b) =>
          block_if(atomic) {
            lambda; block { name(x); colon; eta_typ(ty) }; comma
            term(b, bounds = x :: bounds)
          }
        case Term.OFCLASS(t, c) =>
          block_if(atomic) {
            name(class_kind(c)); space; typ(t, atomic = true)
          }
        case Term.App(a, b) =>
          block_if(atomic) {
            term(a, bounds = bounds, atomic = true)
            space
            term(b, bounds = bounds, atomic = true)
          }
      }
    }

    def proof(prf: Term.Proof,
      bounds: List[String] = Nil,
      bounds_proof: List[String] = Nil,
      atomic: Boolean = false)
    {
      prf match {
        case Term.PBound(i) =>
          try { name(bounds_proof(i)) }
          catch {
            case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i)
          }
        case Term.Abst(x, ty, b) =>
          block_if(atomic) {
            lambda; block { name(x); colon; eta_typ(ty) }; comma
            proof(b, bounds = x :: bounds, bounds_proof)
          }
        case Term.AbsP(x, hy, b) =>
          block_if(atomic) {
            lambda; block { name(x); colon; eps_term(hy, bounds = bounds) }; comma
            proof(b, bounds = bounds, bounds_proof = x :: bounds_proof)
          }
        case Term.Appt(a, b) =>
          block_if(atomic) {
            proof(a, bounds = bounds, bounds_proof = bounds_proof, atomic = true)
            space
            term(b, bounds = bounds, atomic = true)
          }
        case Term.AppP(a, b) =>
          block_if(atomic) {
            proof(a, bounds = bounds, bounds_proof = bounds_proof, atomic = true)
            space
            proof(b, bounds = bounds, bounds_proof = bounds_proof, atomic = true)
          }
        case axm: Term.PAxm =>
          block_if(atomic && axm.types.nonEmpty) {
            name(axiom_kind(axm.name))
            for (ty <- axm.types) { space; typ(ty, atomic = true) }
          }
        case box: Term.PThm =>
          block_if(atomic && box.types.nonEmpty) {
            name(proof_kind(box.serial))
            for (ty <- box.types) { space; typ(ty, atomic = true) }
          }

        case _ => isabelle.error("Bad proof term encountered:\n" + prf)
      }
    }

    def eps_term(t: Term.Term, bounds: List[String] = Nil, atomic: Boolean = false)
    {
      block_if(atomic) { eps; space; term(t, bounds = bounds, atomic = true) }
    }


    /* type classes */

    def class_decl(c: String)
    {
      symbol_const; name(class_kind(c)); colon
      Type; to; eta; space; name(type_kind(Pure_Thy.PROP))
      nl
    }


    /* types */

    def type_decl(c: String, args: Int)
    {
      symbol_const; name(type_kind(c)); colon
      for (_ <- 0 until args) { Type; to }; Type
      nl
    }

    def type_abbrev(c: String, args: List[String], rhs: Term.Typ)
    {
      definition; name(type_kind(c))
      for (a <- args) { space; block { name(a); colon; Type } }
      colon; Type; dfn; typ(rhs)
      nl
    }


    /* arguments */

    def polymorphic(binder: => Unit, typargs: List[String])
    {
      if (typargs.nonEmpty) {
        binder
        for (a <- typargs) { block { name(a); colon; Type }; space }; comma
      }
    }

    def parameters(binder: => Unit, args: List[(String, Term.Typ)])
    {
      if (args.nonEmpty) {
        binder
        for ((x, ty) <- args) { block { name(x); colon; eta_typ(ty) }; space }; comma
      }
    }


    /* consts */

    def const_decl(c: String, typargs: List[String], ty: Term.Typ)
    {
      symbol_const; name(const_kind(c)); colon; polymorphic(all, typargs); eta_typ(ty)
      nl
    }

    def const_abbrev(c: String, typargs: List[String], ty: Term.Typ, rhs: Term.Term)
    {
      definition; name(const_kind(c))
      for (a <- typargs) { space; block { name(a); colon; Type } }
      colon; eta_typ(ty); dfn; term(rhs)
      nl
    }


    /* theorems and proof terms */

    def stmt_decl(
      c: String,
      prop: Export_Theory.Prop,
      proof_term: Option[Term.Proof],
      k: Export_Theory.Kind.Value)
    {
      if (proof_term.isEmpty) symbol_const else definition

      name(kind(c, k)); colon
      polymorphic(all, prop.typargs.map(_._1))
      parameters(all, prop.args)
      eps_term(prop.term)
      nl

      for (prf <- proof_term) {
        dfn
        nl
        polymorphic(lambda, prop.typargs.map(_._1))
        parameters(lambda, prop.args)
        proof(prf)
        nl
      }
    }

    private var exported_proofs = Set.empty[Long]

    def proof_decl(
      id: Export_Theory.Thm_Id,
      read_proof: Export_Theory.Thm_Id => Option[Export_Theory.Proof])
    {
      if (!exported_proofs(id.serial)) {
        for (prf <- read_proof(id)) {
          exported_proofs += id.serial
          stmt_decl(id.serial.toString, prf.prop, Some(prf.proof), Export_Theory.Kind.PROOF)
        }
      }
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
      rule; eta; space; block { name(type_kind(Pure_Thy.FUN)); string(" &a &b") }; rew;
        eta; string(" &a"); to; eta; string(" &b"); nl
    }

    def prelude_prop
    {
      symbol; eps; colon; eta; space; name(type_kind(Pure_Thy.PROP)); to; TYPE; nl
    }

    def prelude_all
    {
      rule; eps; space; block { name(const_kind(Pure_Thy.ALL)); string(" &a &b") }; rew;
        all; block { string("x"); colon; eta; string(" &a") }; comma; eps; string(" (&b x)"); nl
    }

    def prelude_imp
    {
      rule; eps; space; block { name(const_kind(Pure_Thy.IMP)); string(" &a &b") }; rew;
        eps; string(" &a"); to; eps; string(" &b"); nl
    }
  }
}
