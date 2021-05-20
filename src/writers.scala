/** Concrete syntax for various lambda-Pi implementations **/
/*
  For Dedukti lp syntax
  see https://github.com/Deducteam/lambdapi/blob/master/doc/syntax.bnf
*/


package lambdapi

import isabelle.{Exn, File, Library, Path, Symbol, UTF8, error}
import lambdapi.Syntax._

import java.io.{BufferedWriter, FileOutputStream, OutputStreamWriter, Writer}
import scala.collection.mutable.{Map => MutableMap}


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

  def is_regular_identifier(ident: String): Boolean

  def escape(ident: String): String =
    if (ident.containsSlice("|}")) Exn.error("Bad ident: " + Library.quote(ident))
    else f"{|$ident|}"

  def escape_if_needed(a: String): String =
    if (reserved(a) || !is_regular_identifier(a)) escape(a)
    else a
}


abstract class AbstractWriter(writer: Writer) extends IdentWriter
{
  def write(c: Char):   Unit = writer.write(c)
  def write(s: String): Unit = writer.write(s)

  def space = write(' ')
  def nl    = write('\n')

  def lpar  = write('(')
  def rpar  = write(')')
  def colon = write(" : ")

  def block(body: => Unit): Unit = { lpar; body; rpar }
  def block_if(curNot: Syntax.Notation, prevNot: Syntax.Notation, right: Boolean = false, force_no: Boolean = false)(body: => Unit): Unit =
  {
    val prio1: Float = getPriority (curNot).getOrElse(isabelle.error("NotImplemented"))
    val prio2: Float = getPriority(prevNot).getOrElse(isabelle.error("NotImplemented"))

    val doBlock = curNot match {
      case _ if prio1 < prio2 => true
      case _ if prio1 > prio2 => false
      case _ if curNot != prevNot => true
      case Prefix(_, _) => true
      case Infix (_, _) => true
      case InfixL(_, _) => right
      case InfixR(_, _) => !right
      case Quantifier(_) => isabelle.error("NotImplemented")
    }
    if (doBlock && !force_no)
      block(body)
    else
      body
  }

  def ident(a: String): Unit = write(escape_if_needed(a))

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = absNotation, no_impl: Boolean = false, right: Boolean = false): Unit

  def arg(a: Syntax.BoundArg, block: Boolean, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    if (block) {
      if (a.implicit_arg) {
        write("{")
      } else {
        write("(")
      }
    }
    a.id match {
      case Some(id) => ident(id)
      case None => write('_')
    }
    for (ty <- a.typ) { colon; term(ty, notations) }
    if (block) {
      if (a.implicit_arg) {
        write("}")
      } else {
        write(")")
      }
    }
  }

  def comment(c: String)
  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation])
}


class LPWriter(root_path: Path, use_notations: Boolean, writer: Writer) extends AbstractWriter(writer)
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
      "with",
      "≔",
      "→",
      "`",
      ",",
      ":",
      "≡",
      "↪",
      "λ",
      "{",
      "(",
      "[",
      "Π",
      "}",
      ")",
      "]",
      ";",
      "⊢",
      "|",
      "_",
      "?",
      "$",
      "@",
    )

  def is_regular_identifier(ident: String): Boolean =
    ident.nonEmpty &&
      ident.forall(c => !" ,;\r\t\n(){}[]:.`\"".contains(c))

  override def escape(ident: String): String = {
    val pattern = """:(\d+)""".r
    val matched = pattern.findFirstMatchIn(ident)
    matched match {
      case Some(m) =>
        f"🖇${m.group(1)}🖇"
      case None =>
        super.escape(ident)
    }
  }



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
  def end_command = { semicolon; nl }

  def appl(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation, no_impl: Boolean = false, right: Boolean): Unit = {
    val (head, pre_spine) = Syntax.destruct_appls(t)
    val spine = pre_spine.filter(!_._2).map(_._1)
    val contains_impl_arg = pre_spine.exists(_._2)
    head match {
      case Syntax.Symb(id) if notations contains id =>
        val not = notations(id)
        val op = getOperator(not)
        (not, spine) match {
          case (Syntax.Quantifier(_), _) => isabelle.error("NotImplemented")
          case (Syntax.Prefix(op, _), List(arg)) if !(no_impl && contains_impl_arg) =>
          block_if(not, prevNot, right)({
            ident(op)
            space
            term(arg, notations, not, no_impl)
          })
          case (Syntax.Infix(_, _) | Syntax.InfixL(_, _) | Syntax.InfixR(_, _), List(arg1, arg2)) if !(no_impl && contains_impl_arg) =>
            block_if(not, prevNot, right)({
              val op = getOperator(not) // Ugly Scala where I can't get that from the pattern
              term(arg1, notations, not, no_impl)
              space
              ident(op)
              space
              term(arg2, notations, not, no_impl, right = true)
            })
          case _ =>
            // val op = getOperator(not) Incomprehensible Scala to disallow this
            val not = Syntax.appNotation
            val force_no = pre_spine.isEmpty
            block_if(not, prevNot, right, force_no)({
              block(ident(op))
              for ((arg, impl) <- pre_spine) {
                if (impl) {
                space; write("{"); term(arg, notations, Syntax.justHadPars, no_impl, right = true); write("}")
                } else {
                space; term(arg, notations, not, no_impl, right = true)
                }
              }
            })
          }
      case _ =>
        val not = appNotation
        val force_no = pre_spine.isEmpty
        block_if(not, prevNot, right, force_no)({
          term(head, notations, not, right)
          for ((arg, impl) <- pre_spine) {
            if (impl) {
              space; write("{"); term(arg, notations, Syntax.justHadPars, right = true); write("}")
            } else {
              space;
              term(arg, notations, not, right = true)
            }
          }
        })
    }
  }

  def term_notation(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) if notations contains id =>
        appl(t, notations, prevNot, no_impl, right)
      case Syntax.Symb(id) =>
        ident(id)
      case Syntax.Var(id) =>
        ident(id)
      case Syntax.Appl(_, _, _) =>
        appl(t, notations, prevNot, no_impl, right)
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
          { lambda; arg(a, block = true, notations); comma; term(t, notations, no_impl = no_impl) }
      case Syntax.Prod(Syntax.BoundArg(None, Some(ty1), false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          val op = getOperator(not)
          term(ty1, notations, not, no_impl)
          space; write(op); space // write should be ident, but we allow escaping
          term(ty2, notations, not, no_impl, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
          { pi; arg(a, block = true, notations); comma; term(t, notations, absNotation, no_impl) }
    }

  def term_no_notation(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
                       prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) if notations contains id =>
        error("There should be no notations in this mode")
      case Syntax.Symb(id) =>
        ident(id)
      case Syntax.Var(id) =>
        ident(id)
      case Syntax.Appl(t1, t2, isImplicit) =>
        val not = appNotation
        block_if(not, prevNot, right) {
          term(t1, notations, not)
          space
          val newNot = if (isImplicit) justHadPars else appNotation
          if (isImplicit) write("{")
          term(t2, notations, newNot, right = true)
          if (isImplicit) write("}")
        }
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
        { lambda; arg(a, block = true, notations); comma; term(t, notations) }
      case Syntax.Prod(Syntax.BoundArg(None, Some(ty1), false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          val op = getOperator(not)
          term(ty1, notations, not)
          space; write(op); space // write should be ident, but we allow escaping
          term(ty2, notations, not, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(Syntax.absNotation, prevNot, right)
        { pi; arg(a, block = true, notations); comma; term(t, notations, absNotation) }
    }

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    if (use_notations)
      term_notation(t, notations, prevNot, no_impl, right)
    else
      term_no_notation(t, notations, prevNot, no_impl, right)

  def comment(c: String): Unit = {
    write("// " + c)
    nl
  }

  def patternize(t: Syntax.Term, vars: Set[Ident]): Syntax.Term =
    t match {
      case Syntax.TYPE => t
      case Syntax.Symb(_) => t
      case Syntax.Var(id) if vars(id) => Syntax.Var("$" + id)
      case Syntax.Var(_) => t
      case Syntax.Appl(t1, t2, b) => Syntax.Appl(patternize(t1, vars), patternize(t2, vars), b)
      case Syntax.Abst(a @ BoundArg(Some(id), _, _), t) => Syntax.Abst(patternize_arg(a, vars), patternize(t, vars - id))
      case Syntax.Abst(a, t) => Syntax.Abst(patternize_arg(a, vars), patternize(t, vars))
      case Syntax.Prod(a @ BoundArg(Some(id), _, _), t) => Syntax.Prod(patternize_arg(a, vars), patternize(t, vars - id))
      case Syntax.Prod(a, t) => Syntax.Prod(patternize_arg(a, vars), patternize(t, vars))
    }

  def patternize_arg(a: Syntax.BoundArg, vars: Set[Ident]): Syntax.BoundArg =
    a match {
      case BoundArg(id, ty, impl) => BoundArg(id, ty.map(patternize(_, vars)), impl)
    }

  def notation(fullId: Ident, notation: Notation, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    notations(fullId) = notation
    write ("notation ")
    notation match {
      case Prefix(op, priority) => ident(op); space; write("prefix");      space; write(priority.toString)
      case Infix (op, priority) => ident(op); space; write("infix");       space; write(priority.toString)
      case InfixL(op, priority) => ident(op); space; write("infix left");  space; write(priority.toString)
      case InfixR(op, priority) => ident(op); space; write("infix right"); space; write(priority.toString)
      case Quantifier(op) => ident(op); space; write("quantifier")
    }
  }

  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val vars_set = Set.from(vars)
        write("rule ")
        term(patternize(lhs, vars_set), notations, no_impl = true)
        hook_arrow
        term(patternize(rhs, vars_set), notations, no_impl = true)
      case Syntax.Declaration(id, args, ty, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        write("constant ")
        write("symbol ")
        not_opt.fold(ident(id))(not => ident(getOperator(not))) // ident(id) TODO: Ugly
        for (a <- args) { space; arg(a, block = true, notations) }
        colon; term(ty, notations)
        for (not <- not_opt) { end_command; notation(id, not, notations) }
      case Syntax.DefableDecl(id, ty, inj, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        if (inj) { write("injective ") }
        write("symbol ")
        not_opt.fold(ident(id))(not => ident(getOperator(not))) // ident(id) TODO: Ugly
        colon; term(ty, notations)
        for (not <- not_opt) { end_command; notation(id, not, notations) }
      case Syntax.Definition(id, args, ty, tm, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        write("symbol ")
        not_opt.fold(ident(id))(not => ident(getOperator(not))) // ident(id) TODO: Ugly
        for (a <- args) { space; arg(a, block = true, notations) }
        for (ty <- ty) { colon; term(ty, notations) }
        colon_equal; term(tm, notations)
        for (not <- not_opt) { end_command; notation(id, not, notations) }
      case Syntax.Theorem(id, args, ty, prf) =>
        write("opaque symbol ")
        ident(id)
        for (a <- args) { space; arg(a, block = true, notations) }
        colon; term(ty, notations)
        colon_equal; term(prf, notations)
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

  def is_regular_identifier(ident: String): Boolean =
    ident.nonEmpty &&
      ident(0) != '\'' &&
      ident.forall(c => Symbol.is_ascii_letter(c) || Symbol.is_ascii_digit(c) || "_!?'".contains(c))

  def dot    = write('.')
  def lambda = write("\\ ")
  def pi     = write("! ")
  def dfn    = write(" := ")
  def ar_lam = write(" => ")
  def ar_pi  = write(" -> ")
  def ar_rew = write(" --> ")

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation] = MutableMap(),
           prevNot: Notation = absNotation, no_impl: Boolean = false, right: Boolean = false): Unit =
    t match {
      case Syntax.TYPE =>
        write("Type")
      case Syntax.Symb(id) =>
        ident(id)
      case Syntax.Var(id) =>
        ident(id)
      case Syntax.Appl(_, _, _) =>
        block_if(appNotation, prevNot, right) {
          val (head, spine) = Syntax.destruct_appls(t)
          term(head, prevNot = appNotation)
          for ((s, _) <- spine) { space; term(s, prevNot = appNotation, right = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(absNotation, prevNot, right) { arg(a, block = false, notations); ar_lam; term(t) }
      case Syntax.Prod(a, t) =>
        block_if(absNotation, prevNot, right) { arg(a, block = false, notations); ar_pi ; term(t) }
    }

  def comment(c: String)
  {
    write("(; " + c + " ;)")
    nl
  }

  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation] = MutableMap())
  {
    c match {
      case Syntax.Declaration(id, args, ty, _) =>
        ident(id)
        for (a <- args) { space; block {
          arg(a, block = false, notations)
        } }
        colon; term(ty)
      case Syntax.DefableDecl(id, ty, _, _) =>
        write("def ")
        ident(id)
        colon; term(ty)
      case Syntax.Definition(id, args, ty, tm, _) =>
        write("def ")
        ident(id)
        for (a <- args) { space; block {
          arg(a, block = false, notations)
        } }
        for (ty <- ty) { colon; term(ty) }
        dfn; term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("thm ")
        ident(id)
        for (a <- args) { space; block {
          arg(a, block = false, notations)
        } }
        colon; term(ty)
        dfn; term(prf)
      case Syntax.Rewrite(vars, lhs, rhs) =>
        if (vars.nonEmpty) write("[" + vars.mkString(sep = ", ") + "] ")
        term(lhs)
        ar_rew; term(rhs)
    }
    dot
    nl
  }
}
