/** Concrete syntax for various lambda-Pi implementations **/
/*
  For Dedukti lp syntax
  see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf
*/


package lambdapi

import isabelle.{Exn, File, Library, Path, Symbol, UTF8}
import lambdapi._


import java.io.{BufferedWriter, FileOutputStream, OutputStreamWriter, Writer}


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

  def is_regular_identifier(ident: String): Boolean =
    ident.nonEmpty &&
    { val c = ident(0); Symbol.is_ascii_letter(c) || c == '_' || c == '\'' } &&
    ident.forall(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || c == '_' || c == '+' || c == '\'') // TODO: Tidy it up

  def escape(ident: String): String =
    if (ident.containsSlice("|}")) Exn.error("Bad ident: " + Library.quote(ident))
    else {
      val pattern = """:(\d+)""".r
      val matched = pattern.findFirstMatchIn(ident)
      matched match {
        case Some(m) =>
          f"£${m.group(1)}£"
        case None =>
          f"{|$ident|}"
      }
    }

  def escape_if_needed(a: String): String =
    if (reserved(a) || !is_regular_identifier(a)) escape(a)
    else a
}


abstract class AbstractWriter(writer: Writer) extends IdentWriter
{
  def write(c: Char):   Unit = writer.write(c)
  def write(s: String): Unit = writer.write(s)

  def space = write(' ')
  def nl = write('\n')

  def lpar = write('(')
  def rpar = write(')')
  def colon = write(" : ")

  def block(body: => Unit): Unit = { lpar; body; rpar }
  def block_if(curNot: Syntax.Notation, prevNot: Syntax.Notation, right: Boolean = false): (=> Unit) => Unit =
  {
    val prio1: Float = getPriority (curNot).getOrElse(isabelle.error("NotImplemented"))
    val prio2: Float = getPriority(prevNot).getOrElse(isabelle.error("NotImplemented"))

    curNot match {
      case _ if prio1 < prio2 => body => block(body)
      case _ if prio1 > prio2 => body => body
      case _ if curNot != prevNot => body => block(body)
      case Prefix(_, _) => body => block(body)
      case Infix (_, _) => body => block(body)
      case InfixL(_, _) if !right => body => body
      case InfixL(_, _) if  right => body => block(body)
      case InfixR(_, _) if !right => body => block(body)
      case InfixR(_, _) if  right => body => body
      case Quantifier(_) => isabelle.error("NotImplemented")
    }
  }

  def ident(a: String): Unit = write(escape_if_needed(a))

  def term(t: Syntax.Term, notations: Map[Syntax.Ident, Syntax.Notation] = Map(), prevNot: Notation, right: Boolean = false)

  def arg(a: Syntax.Arg, notations: Map[Syntax.Ident, Syntax.Notation] = Map())
  {
    a.id match {
      case Some(id) => ident(id)
      case None => write('_')
    }
    for (ty <- a.typ) { colon; term(ty, notations) }
  }

  def comment(c: String)
  def command(c: Syntax.Command)
}


class LPWriter(root_path: Path, writer: Writer) extends AbstractWriter(writer)
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
  def end_command = semicolon; nl

  def appl(t1: Syntax.Term, t2: Syntax.Term, notations: Map[Syntax.Ident, Syntax.Notation], prevNot: Notation, right: Boolean): Unit = {
    val (head, spine) = Syntax.dest_appls(t1, List(t2))
    head match {
      case Syntax.Symb(id) if notations contains id =>
        val not = notations(id)
        block_if(not, prevNot, right) {
          (not, spine) match {
            case (Syntax.Prefix(op, _), List(arg)) =>
              ident(op)
              term(arg, notations, not)
            case (Syntax.Quantifier(_), _) => isabelle.error("NotImplemented")
            case (Syntax.Infix(_, _) | Syntax.InfixL(_, _) | Syntax.InfixR(_, _), List(arg1, arg2)) =>
              val op = getOperator(not)
              term(arg1, notations, not)
              space;
              ident(op);
              space
              term(arg2, notations, not, right = true)
          }
        }
      case _ =>
        term(head, notations, prevNot, right)
        for (arg <- spine) {
          space; term(arg, notations, Syntax.appNotation, right = true)
        }
    }
  }

  def term(t: Syntax.Term, notations: Map[Syntax.Ident, Syntax.Notation] = Map(), prevNot: Notation, right: Boolean = false)
  {
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) =>
        ident(id)
      case Syntax.Var(id) =>
        ident(id)
      case Syntax.Appl(t1, t2) =>
        appl(t1, t2, notations, prevNot, right)
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
          { lambda; block { arg(a) }; comma; term(t, notations, Syntax.absNotation, right = true) }
      case Syntax.Prod(Syntax.Arg(None, Some(ty1), false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          val op = getOperator(not)
          term(ty1, notations, not)
          space; ident(op); space
          term(ty2, notations, not, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
          { pi;     block { arg(a) }; comma; term(t, notations, Syntax.absNotation, right = true) }
    }
  }

  def comment(c: String): Unit = {
    write("// " + c)
    nl
  }

  def patternize(t: Syntax.Term, vars: Set[Ident]): Syntax.Term = {
    t match {
      case Syntax.TYPE => t
      case Syntax.Symb(id) => t
      case Syntax.Var(id) if vars(id) => Syntax.Var("$" + id)
      case Syntax.Var(id) => t
      case Syntax.Appl(t1, t2) => Syntax.Appl(patternize(t1, vars), patternize(t2, vars))
      case Syntax.Abst(Arg(Some(id), _, _) as a, t) => Syntax.Abst(a, patternize(t, vars - id))
      case Syntax.Abst(a, t) => Syntax.Abst(a, patternize(t, vars))
      case Syntax.Prod(Arg(Some(id), _, _) as a, t) => Syntax.Prod(a, patternize(t, vars - id))
      case Syntax.Prod(a, t) => Syntax.Prod(a, patternize(t, vars))
    }
  }

  def notation(fullId: Ident, notation: Notation): Unit = {
    write ("notation ")
    notation match {
      case Prefix(op, priority) => ident(op); write("prefix"); write(priority.toString)
      case Infix (op, priority) => ident(op); write("infix"); write(priority.toString)
      case InfixL(op, priority) => ident(op); write("infix left"); write(priority.toString)
      case InfixR(op, priority) => ident(op); write("infix right"); write(priority.toString)
      case Quantifier(op) => ident(op); write("quantifier")
    }
    colon_equal; term(Syntax.Symb(fullId))
  }

  def command(c: Syntax.Command): Unit = {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val vars_set = Set.from(vars)
        write("rule ")
        term(patternize(lhs, vars_set))
        hook_arrow
        term(patternize(rhs, vars_set))
      case Syntax.Declaration(id, args, ty, not_opt) =>
        write("constant ")
        write("symbol ")
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        colon; term(ty)
        for (not <- not_opt) { end_command; notation(id, not) }
      case Syntax.DefableDecl(id, ty, not_opt) =>
        write("symbol ")
        ident(id)
        colon; term(ty)
        for (not <- not_opt) { end_command; notation(id, not) }
      case Syntax.Definition(id, args, ty, tm, not_opt) =>
        write("symbol ")
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        for (ty <- ty) { colon; term(ty) }
        colon_equal; term(tm)
        for (not <- not_opt) { end_command; notation(id, not) }
      case Syntax.Theorem(id, args, ty, prf) =>
        write("opaque symbol ")
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        colon; term(ty)
        colon_equal; term(prf)
    }
    end_command
  }

  def eta_equality()
  {
    write("""flag "eta_equality" on""")
    semicolon; nl
  }

  def require_open(module: String)
  {
    write("require open " + root + ".")
    ident(module)
    semicolon; nl
  }
}


class DKWriter(writer: Writer) extends AbstractWriter(writer)
{
  val reserved =
    Set(
      "def",
      "thm",
      "Type",
      "_")

  def dot    = write('.')
  def lambda = write("\\ ")
  def pi     = write("! ")
  def dfn    = write(" := ")
  def ar_lam = write(" => ")
  def ar_pi  = write(" -> ")
  def ar_rew    = write(" --> ")

  def term(t: Syntax.Term, notations: Map[Syntax.Ident, Syntax.Notation] = Map(), atomic: Notation = absNotation)
  {
    t match {
      case Syntax.TYPE =>
        write("Type")
      case Syntax.Symb(id) =>
        ident(id)
      case Syntax.Var(id) =>
        ident(id)
      case Syntax.Appl(t1, t2) =>
        block_if(appNotation, atomic) {
          val (head, spine) = Syntax.dest_appls(t1, List(t2))
          term(head, atomic = true)
          for (s <- spine) { space; term(s, atomic = appNotation) }
        }
      case Syntax.Abst(a, t) =>
        block_if(atomic) { arg(a); ar_lam; term(t) }
      case Syntax.Prod(a, t) =>
        block_if(atomic) { arg(a); ar_pi ; term(t) }
    }
  }

  def comment(c: String)
  {
    write("(; " + c + " ;)")
    nl
  }

  def command(c: Syntax.Command)
  {
    c match {
      case Syntax.Declaration(id, args, ty, _) =>
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        colon
        term(ty)
      case Syntax.DefableDecl(id, ty, _) =>
        write("def ")
        ident(id)
        colon
        term(ty)
      case Syntax.Definition(id, args, ty, tm, _) =>
        write("def ")
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        for (ty <- ty) { colon; term(ty) }
        dfn
        term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("thm ")
        ident(id)
        for (a <- args) { space; block { arg(a) } }
        colon; term(ty)
        dfn
        term(prf)
      case Syntax.Rewrite(vars, lhs, rhs) =>
        if (vars.nonEmpty) write("[" + vars.mkString(sep = ", ") + "] ")
        term(lhs)
        ar_rew
        term(rhs)
    }
    dot
    nl
  }
}
