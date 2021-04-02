/** Concrete syntax for various lambda-Pi implementations **/
/*
  For Dedukti lp syntax
  see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf
*/


package lambdapi

import isabelle.{File, Exn, Library, Path, Symbol, UTF8}
import lambdapi._

import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter, Writer}


class PartWriter(file: Path) extends Writer
{
  private val file_part = file.ext("part")

  private val w =
    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file_part.file), UTF8.charset))

  def write(c: Char) { w.write(c) }
  def write(a: Array[Char], off: Int, len: Int) { w.write(a, off, len) }
  def flush() { w.flush() }

  def close()
  {
    w.close()
    File.move(file_part, file)
  }
}


trait IdentWriter
{
  val reserved: Set[String]

  def is_regular_identifier(name: String): Boolean =
    name.nonEmpty &&
    { val c = name(0); Symbol.is_ascii_letter(c) || c == '_' } &&
    name.forall(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_')

  def escape(name: String): String =
    if (name.containsSlice("|}")) Exn.error("Bad name: " + Library.quote(name))
    else {
      val pattern = """:(\d+)""".r
      val matched = pattern.findFirstMatchIn(name)
      matched match {
        case Some(m) =>
          f"£${m.group(1)}£"
        case None =>
          f"{|${name}|}"
      }
    }

  def escape_if_needed(a: String): String =
    if (reserved(a) || !is_regular_identifier(a)) escape(a)
    else a
}


abstract class LambdaPiWriter(writer: Writer) extends IdentWriter
{
  def write(c: Char) = writer.write(c)
  def write(s: String) = writer.write(s)

  def space = write(' ')
  def nl = write('\n')

  def bg = write('(')
  def en = write(')')
  def colon = write(" : ")

  def block(body: => Unit) { bg; body; en }
  def block_if(atomic: Boolean)(body: => Unit)
  {
    if (atomic) bg
    body
    if (atomic) en
  }

  def name(a: String) = write(escape_if_needed(a))

  def bind(arg: Syntax.Arg, bounds: List[String]) =
    arg match {
      case Syntax.Arg(Some(name), _) => escape_if_needed(name) :: bounds
      case _ => bounds
    }

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false)

  def arg(a: Syntax.Arg, bounds: List[String] = Nil)
  {
    a.id match {
      case Some(id) => name(id)
      case None => write('_')
    }
    for (t <- a.typ) { colon; term(t, bounds) }
  }

  def comment(c: String)
  def write(c: Syntax.Command)
}


class LPWriter(root_path: Path, writer: Writer) extends LambdaPiWriter(writer)
{
  val reserved = // copied from lambdapi/src/parsing/lpLexer.ml lines 185-240
    Set(
      "abort",
      "admit",
      "admitted",
      "apply",
      "as",
      "assert",
      "assertnot",
      "assume",
      "begin",
      "builtin",
      "compute",
      "constant",
      "debug",
      "end",
      "fail",
      "flag",
      "focus",
      "generalize",
      "have",
      "in",
      "induction",
      "inductive",
      "infix",
      "injective",
      "left",
      "let",
      "off",
      "on",
      "opaque",
      "open",
      "prefix",
      "print",
      "private",
      "proofterm",
      "protected",
      "prover",
      "prover_timeout",
      "quantifier",
      "refine",
      "reflexivity",
      "require",
      "rewrite",
      "right",
      "rule",
      "sequential",
      "set",
      "simplify",
      "solve",
      "symbol",
      "symmetry",
      "type",
      "TYPE",
      "unif_rule",
      "verbose",
      "why3",
      "with")

  val root: String = root_path.implode.replace('/', '.')

  def comma       = write(", ")
  def semicolon   = write(";")
  def arrow       = write(" \u2192 ") // →
  def colon_equal = write(" \u2254 ") // ≔
  def equiv       = write(" \u2261 ") // ≡
  def hook_arrow  = write(" \u21aa ") // ↪
  def lambda      = write("\u03bb ")  // λ
  def pi          = write("\u03a0 ")  // Π
  def turnstile   = write(" \u22a2 ") // ⊢

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false)
  {
    t match {
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
          val (head, spine) = Syntax.dest_appls(t1, List(t2))
          term(head, bounds, atomic = true)
          for (s <- spine) { space; term(s, bounds, atomic = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(atomic) { lambda; block { arg(a, bounds) }; comma; term(t, bind(a, bounds)) }
      case Syntax.Prod(a, t) =>
        block_if(atomic) { pi;     block { arg(a, bounds) }; comma; term(t, bind(a, bounds)) }
    }
  }

  def comment(c: String)
  {
    write("// " + c)
    nl
  }

  def write(c: Syntax.Command)
  {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val pat_vars = vars.map(v => "$" + v)
        write("rule ")
        term(lhs, pat_vars)
        hook_arrow
        term(rhs, pat_vars)
      case Syntax.Declaration(id, args, ty, const) =>
        if (const) write("constant ")
        write("symbol ")
        name(id)
        for (a <- args) { space; block { arg(a) } }
        colon
        term(ty)
      case Syntax.Definition(id, args, ty, tm) =>
        write("symbol ");
        name(id)
        for (a <- args) { space; block { arg(a) } }
        for (ty <- ty) { colon; term(ty) }
        colon_equal
        term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("symbol ");
        name(id)
        for (a <- args) { space; block { arg(a) } }
        colon; term(ty)
        colon_equal
        term(prf)
    }
    semicolon; nl
  }

  def eta_equality()
  {
    write("""flag "eta_equality" on""")
    semicolon; nl
  }

  def require_open(module: String)
  {
    write("require open " + root + ".")
    name(module)
    semicolon; nl
  }
}


class DKWriter(writer: Writer) extends LambdaPiWriter(writer)
{
  val reserved =
    Set(
      "def",
      "thm",
      "_")

  def dot    = write('.')
  def lambda = write("\\ ")
  def pi     = write("! ")
  def dfn    = write(" := ")
  def ar_lam = write(" => ")
  def ar_pi  = write(" -> ")
  def rew    = write(" --> ")

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false)
  {
    t match {
      case Syntax.TYPE =>
        write("Type")
      case Syntax.Symb(id) =>
        name(id)
      case Syntax.FVar(id) =>
        assert(!bounds.contains(escape_if_needed(id)))
        name(id)
      case Syntax.BVar(idx) =>
        write(bounds(idx))
      case Syntax.Appl(t1, t2) =>
        block_if(atomic) {
          val (head, spine) = Syntax.dest_appls(t1, List(t2))
          term(head, bounds, atomic = true)
          for (s <- spine) { space; term(s, bounds, atomic = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(atomic) { arg(a, bounds); ar_lam; term(t, bind(a, bounds)) }
      case Syntax.Prod(a, t) =>
        block_if(atomic) { arg(a, bounds); ar_pi ; term(t, bind(a, bounds)) }
    }
  }

  def comment(c: String)
  {
    write("(; " + c + " ;)")
    nl
  }

  def write(c: Syntax.Command)
  {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        if (!vars.isEmpty) write("[" + vars.mkString(sep = ", ") + "] ")
        term(lhs, vars)
        rew
        term(rhs, vars)
      case Syntax.Declaration(id, args, ty, const) =>
        if (!const) write("def ")
        name(id)
        for (a <- args) { space; block { arg(a) } }
        colon
        term(ty)
      case Syntax.Definition(id, args, ty, tm) =>
        write("def ");
        name(id)
        for (a <- args) { space; block { arg(a) } }
        for (ty <- ty) { colon; term(ty) }
        dfn
        term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("thm ");
        name(id)
        for (a <- args) { space; block { arg(a) } }
        colon; term(ty)
        dfn
        term(prf)
    }
    dot
    nl
  }
}
