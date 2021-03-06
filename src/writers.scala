/** Concrete syntax for various lambda-Pi implementations **/
/*
  For Dedukti lp syntax
  see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf
*/

package isabelle.dedukti

import isabelle._


import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter, Writer}
import java.nio.file.{Files, StandardCopyOption}


class Part_Writer(file: Path) extends Writer
{
  private val file_part = file.ext("part")

  private val writer =
    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file_part.file), UTF8.charset))

  def write(c: Char): Unit = writer.write(c)
  def write(a: Array[Char], off: Int, len: Int): Unit = writer.write(a, off, len)
  def flush(): Unit = writer.flush()

  def close(): Unit =
  {
    writer.close()
    Files.move(file_part.file.toPath, file.file.toPath, StandardCopyOption.REPLACE_EXISTING)
  }
}


trait Ident_Writer
{
  val reserved: Set[String]

  def is_regular_identifier(name: String): Boolean =
    name.nonEmpty &&
    { val c = name(0); Symbol.is_ascii_letter(c) || c == '_' } &&
    name.forall(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_')

  def escape(name: String): String =
    if (name.containsSlice("|}")) Exn.error("Bad name: " + Library.quote(name))
    else "{|" + name + "|}"

  def escape_if_needed(a: String): String =
    if (reserved(a) || !is_regular_identifier(a)) escape(a)
    else a
}


abstract class LambdaPi_Writer(writer: Writer) extends Ident_Writer
{
  def write(c: Char): Unit = writer.write(c)
  def write(s: String): Unit = writer.write(s)

  def space(): Unit = write(' ')
  def nl(): Unit = write('\n')

  def bg(): Unit = write('(')
  def en(): Unit = write(')')
  def colon(): Unit = write(" : ")

  def block(body: => Unit): Unit = { bg(); body; en() }
  def block_if(atomic: Boolean)(body: => Unit): Unit =
  {
    if (atomic) bg()
    body
    if (atomic) en()
  }

  def name(a: String): Unit = write(escape_if_needed(a))

  def bind(arg: Syntax.Arg, bounds: List[String]): List[String] =
    arg match {
      case Syntax.Arg(Some(name), _) => escape_if_needed(name) :: bounds
      case _ => bounds
    }

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false): Unit

  def arg(a: Syntax.Arg, bounds: List[String] = Nil): Unit =
  {
    a.id match {
      case Some(id) => name(id)
      case None => write('_')
    }
    for (t <- a.typ) { colon(); term(t, bounds) }
  }

  def comment(c: String): Unit
  def write(c: Syntax.Command): Unit
}


class LP_Writer(writer: Writer) extends LambdaPi_Writer(writer)
{
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

  def comma(): Unit = write(", ")
  def to(): Unit = write(" \u21d2 ")
  def rew(): Unit = write(" \u2192 ")
  def dfn(): Unit = write(" \u2254 ")
  def lambda(): Unit = write("\u03bb ")
  def forall(): Unit = write("\u2200 ")

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false): Unit =
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
          for (s <- spine) { space(); term(s, bounds, atomic = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(atomic) { lambda(); block { arg(a, bounds) }; comma(); term(t, bind(a, bounds)) }
      case Syntax.Prod(a, t) =>
        block_if(atomic) { forall(); block { arg(a, bounds) }; comma(); term(t, bind(a, bounds)) }
    }
  }

  def comment(c: String): Unit =
  {
    write("// " + c)
    nl()
  }

  def write(c: Syntax.Command): Unit =
  {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val ampvars = vars.map(v => "&" + v)
        write("rule ")
        term(lhs, ampvars)
        rew()
        term(rhs, ampvars)
      case Syntax.Declaration(id, args, ty, const) =>
        write("symbol ")
        if (const) write("const ")
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        colon()
        term(ty)
      case Syntax.Definition(id, args, ty, tm) =>
        write("definition ");
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        for (ty <- ty) { colon(); term(ty) }
        dfn()
        term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("theorem ");
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        colon(); term(ty)
        write(" proof refine ")
        term(prf)
        write(" qed")
    }
    nl()
  }

  def eta_equality(): Unit =
  {
    write("""set flag "eta_equality" on""")
    nl()
  }

  def require_open(module: String): Unit =
  {
    write("require open ")
    name(module)
    nl()
  }
}


class DK_Writer(writer: Writer) extends LambdaPi_Writer(writer)
{
  val reserved =
    Set(
      "def",
      "thm",
      "_")

  def dot(): Unit = write('.')
  def lambda(): Unit = write("\\ ")
  def pi(): Unit = write("! ")
  def dfn(): Unit = write(" := ")
  def ar_lam(): Unit = write(" => ")
  def ar_pi(): Unit = write(" -> ")
  def rew(): Unit = write(" --> ")

  def term(t: Syntax.Term, bounds: List[String] = Nil, atomic: Boolean = false): Unit =
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
          for (s <- spine) { space(); term(s, bounds, atomic = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(atomic) { arg(a, bounds); ar_lam(); term(t, bind(a, bounds)) }
      case Syntax.Prod(a, t) =>
        block_if(atomic) { arg(a, bounds); ar_pi() ; term(t, bind(a, bounds)) }
    }
  }

  def comment(c: String): Unit =
  {
    write("(; " + c + " ;)")
    nl()
  }

  def write(c: Syntax.Command): Unit =
  {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        if (vars.nonEmpty) write("[" + vars.mkString(sep = ", ") + "] ")
        term(lhs, vars)
        rew()
        term(rhs, vars)
      case Syntax.Declaration(id, args, ty, const) =>
        if (!const) write("def ")
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        colon()
        term(ty)
      case Syntax.Definition(id, args, ty, tm) =>
        write("def ");
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        for (ty <- ty) { colon(); term(ty) }
        dfn()
        term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("thm ");
        name(id)
        for (a <- args) { space(); block { arg(a) } }
        colon(); term(ty)
        dfn()
        term(prf)
    }
    dot()
    nl()
  }
}
