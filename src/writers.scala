/** Concrete syntax for various lambda-Pi implementations **/

package isabelle.dedukti

import isabelle._
import isabelle.dedukti.Syntax._

import java.io.{FileOutputStream, OutputStreamWriter, BufferedWriter, Writer}
import java.nio.file.{Files, StandardCopyOption}
import scala.collection.mutable.{Map => MutableMap}

/** Opens a path.part file for writing.
 * @see [[Writer]] */
class Part_Writer(file: Path) extends Writer {
  private val file_part = file.ext("part")

  private val writer =
    new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file_part.file), UTF8.charset))

  def write(c: Char): Unit = writer.write(c)
  def write(a: Array[Char], off: Int, len: Int): Unit = writer.write(a, off, len)
  def flush(): Unit = writer.flush()

  def close(): Unit = {
    writer.close()
    Files.move(file_part.file.toPath, file.file.toPath, StandardCopyOption.REPLACE_EXISTING)
  }
}

/** Tools to write <span style="color:#9932CC;">lambdapi</span> identifiers */
trait Ident_Writer {
  val reserved: Set[String]

  def is_regular_identifier(ident: String): Boolean

  def escape(ident: String): String =
    if (ident.containsSlice("|}")) Exn.error("Bad ident: " + Library.quote(ident))
    else f"{|$ident|}"

  def escape_if_needed(a: String): String = {
    val a1 =
      if (a.startsWith("'")||a.startsWith(":"))
        "_" + a.substring(1,a.length())
      else a
    val a2 = a1.replace('(','_').replace(')','_').replace('\\','_').replace('<','_').replace('>','_').replace('^','_')
    if (reserved(a2) || !is_regular_identifier(a2)) escape(a2) else a2
  }
}

/** Tools for writing in a translated file
 *  <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference dedukti (purple)
 *       $lp: reference lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define metc span style="color:#FFA500;"
 * @define mete /span></code
 * @define metce /span
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define argc span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define argce /span
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
abstract class Abstract_Writer(root: String, writer: Writer) extends Ident_Writer {
  def write(c: Char):   Unit = writer.write(c)
  def write(s: String): Unit = writer.write(s)

  def space() : Unit = write(' ')
  /** Write a newline character */
  def nl()    : Unit = write('\n')

  /** Write a left parenthesis */
  def lpar()  : Unit = write('(')
  /** Write a right parenthesis */
  def rpar()  : Unit = write(')')
  def colon() : Unit = write(" : ")
  
  /** enclose the result of body inside parentheses */
  def block(body: => Unit): Unit = { lpar(); body; rpar() }

  /** To be used while in the middle of writing a term.
   *  Does <$arg>body<$arge>, but may enclose the results inside parentheses depending
   *  on priorities and associativity of notations
   * 
   * @param curNot the $lp notation of the current symbol
   * @param prevNot the $lp notation of the previous symbol
   * @param right If the current notation is infix, whether we are to the right of it or not.
   *              Default: <code>false</code>
   * @param force_no input true to force non-parenthesising, for example when simply
   *                 writing one symbol. Default: <code>false</code>
   * @param body a writing command
   */
  def block_if(
    curNot: Syntax.Notation,
    prevNot: Syntax.Notation,
    right: Boolean = false,
    force_no: Boolean = false)(
    body: => Unit
  ): Unit = {
    val prio1: Double = getPriority (curNot).getOrElse(isabelle.error("NotImplemented"))
    val prio2: Double = getPriority(prevNot).getOrElse(isabelle.error("NotImplemented"))

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
    if (doBlock && !force_no) block(body)
    else body
  }

  def var_ident(a: String): Unit = {
    write(escape_if_needed(a))
  }

  def mod_ident(a: String): Unit = {
    write(root + escape_if_needed(Prelude.mod_name(a)))
  }

  def sym_ident(a: String): Unit = {
    write(escape_if_needed(a))
  }

  def sym_qident(a: String): Unit = {
    write(root + Prelude.mod_name(Prelude.module_of(a)) + "." + escape_if_needed(a))
  }

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = absNotation, no_impl: Boolean = false, right: Boolean = false): Unit

  def arg(a: Syntax.BoundArg, block: Boolean, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    if (block) {
      /*if (a.implicit_arg) {
        write("[")
      } else {*/
        write("(")
      //}
    }
    a.id match {
      case Some(id) => var_ident(id)
      case None => write('_')
    }
    colon()
    term(a.typ, notations, prevNot = justHadPars)
    if (block) {
      if (a.implicit_arg) {
        write("]")
      } else {
        write(")")
      }
    }
  }

  def comment(c: String): Unit
  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit
}

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference dedukti (purple)
 *       $lp: reference lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define metc span style="color:#FFA500;"
 * @define mete /span></code
 * @define metce /span
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define argc span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define argce /span
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
class LP_Writer(use_notations: Boolean, writer: Writer)
  extends Abstract_Writer("Isabelle.", writer) {
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
      "remove",
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

  // Manually escape the name given to unnamed lambda abstraction arguments which doesn't fit lambdapi's rules, even when escaping
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

  def comma()       : Unit = write(", ")
  def semicolon()   : Unit = write(";")
  def arrow()       : Unit = write(" → ")
  def colon_equal() : Unit = write(" ≔ ")
  def equiv()       : Unit = write(" ≡ ")
  def hook_arrow()  : Unit = write(" ↪ ")
  def lambda()      : Unit = write("λ ")
  def pi()          : Unit = write("Π ")
  def turnstile()   : Unit = write(" ⊢ ")
  def end_command() : Unit = { semicolon(); nl() }

  // Terms that are applications (can be a head only), pretty-prints infix operators
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
            sym_qident(op)
            space()
            term(arg, notations, not, no_impl)
          })
          case (Syntax.Infix(_, _) | Syntax.InfixL(_, _) | Syntax.InfixR(_, _), List(arg1, arg2)) if !(no_impl && contains_impl_arg) =>
            block_if(not, prevNot, right)({
              val op = getOperator(not) // Ugly Scala where I can't get that from the pattern
              term(arg1, notations, not, no_impl)
              space()
              sym_qident(op)
              space()
              term(arg2, notations, not, no_impl, right = true)
            })
          case _ =>
            // val op = getOperator(not) Incomprehensible Scala to disallow this
            val not = Syntax.appNotation
            val force_no = pre_spine.isEmpty
            block_if(not, prevNot, right, force_no) {
              block(sym_qident(op))
              for ((arg, impl) <- pre_spine) {
                if (impl) {
                  if (no_impl || spine.isEmpty) { space(); write("["); term(arg, notations, Syntax.justHadPars, no_impl, right = true); write("]") }
                } else {
                space(); term(arg, notations, not, no_impl, right = true)
                }
              }
            }
          }
      case _ =>
        val not = appNotation
        val force_no = pre_spine.isEmpty
        block_if(not, prevNot, right, force_no)({
          term(head, notations, not, right)
          for ((arg, impl) <- pre_spine) {
            if (impl) {
              if (no_impl || spine.isEmpty) { space(); write("["); term(arg, notations, Syntax.justHadPars, right = true); write("]") }
            } else {
              space()
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
        sym_qident(id)
      case Syntax.Var(id) =>
        var_ident(id)
      case Syntax.Appl(_, _, _) =>
        appl(t, notations, prevNot, no_impl, right)
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right) {
          lambda(); arg(a, block = true, notations); comma(); term(t, notations, no_impl = no_impl)
        }
      case Syntax.Prod(Syntax.BoundArg(None, ty1, false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          val op = getOperator(not)
          term(ty1, notations, not, no_impl)
          space(); write(op); space() // write should be ident, but we allow escaping
          term(ty2, notations, not, no_impl, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(Syntax.absNotation, prevNot, right) {
          pi(); arg(a, block = true, notations); comma(); term(t, notations, absNotation, no_impl)
        }
    }

  def term_no_notation(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
                       prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) if notations contains id =>
        error("There should be no notations in this mode")
      case Syntax.Symb(id) =>
        sym_qident(id)
      case Syntax.Var(id) =>
        var_ident(id)
      case Syntax.Appl(t1, t2, isImplicit) =>
        val not = appNotation
        block_if(not, prevNot, right) {
          term(t1, notations, not)
          space()
          val newNot = if (isImplicit) justHadPars else appNotation
          if (isImplicit) write("[")
          term(t2, notations, newNot, right = true)
          if (isImplicit) write("]")
        }
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right) {
          lambda(); arg(a, block = true, notations); comma(); term(t, notations)
        }
      case Syntax.Prod(Syntax.BoundArg(None, ty1, false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          val op = getOperator(not)
          term(ty1, notations, not)
          space(); write(op); space() // write should be ident, but we allow escaping
          term(ty2, notations, not, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(Syntax.absNotation, prevNot, right) {
          pi(); arg(a, block = true, notations); comma(); term(t, notations, absNotation)
        }
    }

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    if (use_notations)
      term_notation(t, notations, prevNot, no_impl, right)
    else
      term_no_notation(t, notations, prevNot, no_impl, right)

  def comment(c: String): Unit = {
    write("// " + c)
    nl()
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
      case BoundArg(id, ty, impl) => BoundArg(id, patternize(ty, vars), impl)
    }

  def notation(fullId: Ident, notation: Notation, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    notations(fullId) = notation
    write ("notation ")
    notation match {
      case Prefix(op, priority) => sym_qident(op); space(); write("prefix");      space(); write(priority.toString)
      case Infix (op, priority) => sym_qident(op); space(); write("infix");       space(); write(priority.toString)
      case InfixL(op, priority) => sym_qident(op); space(); write("infix left");  space(); write(priority.toString)
      case InfixR(op, priority) => sym_qident(op); space(); write("infix right"); space(); write(priority.toString)
      case Quantifier(op) => sym_qident(op); space(); write("quantifier")
    }
  }

  def ident_or_notation(id: Syntax.Ident, not: Option[Syntax.Notation]): Unit = {
    not.fold(sym_ident(id))(not => sym_ident(getOperator(not))) // Ugly
  }

  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val vars_set = Set.from(vars)
        write("rule ")
        term(patternize(lhs, vars_set), notations, no_impl = true)
        hook_arrow()
        term(patternize(rhs, vars_set), notations, no_impl = true)
      case Syntax.Declaration(id, args, ty, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        write("constant ")
        write("symbol ")
        ident_or_notation(id, not_opt)
        for (a <- args) { space(); arg(a, block = true, notations) }
        colon(); term(ty, notations)
        for (not <- not_opt) { end_command(); notation(id, not, notations) }
      case Syntax.DefableDecl(id, ty, inj, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        if (inj) { write("injective ") }
        write("symbol ")
        ident_or_notation(id, not_opt)
        colon(); term(ty, notations)
        for (not <- not_opt) { end_command(); notation(id, not, notations) }
      case Syntax.Definition(id, args, ty, tm, not) =>
        val not_opt: Option[Notation] = if (use_notations) not else None
        write("symbol ")
        ident_or_notation(id, not_opt)
        for (a <- args) { space(); arg(a, block = true, notations) }
        for (ty <- ty) { colon(); term(ty, notations) }
        colon_equal(); term(tm, notations)
        for (not <- not_opt) { end_command(); notation(id, not, notations) }
      case Syntax.Theorem(id, args, ty, prf) =>
        write("opaque symbol ")
        sym_ident(id)
        for (a <- args) { space(); arg(a, block = true, notations) }
        colon(); term(ty, notations)
        colon_equal(); term(prf, notations)
    }
  end_command()
  }

  def eta_equality(): Unit = {
    write("""flag "eta_equality" on""")
    end_command()
  }

  def require(module: String): Unit = {
    write("require ")
    mod_ident(module)
    end_command()
  }
}


class DK_Writer(writer: Writer) extends Abstract_Writer("", writer) {
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

  def dot()    : Unit = write('.')
  def lambda() : Unit = write("\\ ")
  def pi()     : Unit = write("! ")
  def dfn()    : Unit = write(" := ")
  def ar_lam() : Unit = write(" => ")
  def ar_pi()  : Unit = write(" -> ")
  def ar_rew() : Unit = write(" --> ")

  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation] = MutableMap(),
           prevNot: Notation = justHadPars, no_impl: Boolean = false, right: Boolean = false): Unit =
    t match {
      case Syntax.TYPE =>
        write("Type")
      case Syntax.Symb(id) =>
        sym_qident(id)
      case Syntax.Var(id) =>
        var_ident(id)
      case Syntax.Appl(_, _, _) =>
        block_if(appNotation, prevNot, right) {
          val (head, spine) = Syntax.destruct_appls(t)
          term(head, prevNot = appNotation)
          for ((s, _) <- spine) { space(); term(s, prevNot = appNotation, right = true) }
        }
      case Syntax.Abst(a, t) =>
        block_if(absNotation, prevNot, right) { arg(a, block = false, notations); ar_lam(); term(t) }
      case Syntax.Prod(Syntax.BoundArg(None, ty1, false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          term(ty1, notations, not)
          ar_pi()
          term(ty2, notations, not, right = true)
        }
      case Syntax.Prod(a, t) =>
        block_if(absNotation, prevNot, right) { arg(a, block = false, notations); ar_pi() ; term(t) }
    }

  def comment(c: String): Unit = {
    write("(; " + c + " ;)")
    nl()
  }

  def command(
    c: Syntax.Command,
    notations: MutableMap[Syntax.Ident, Syntax.Notation] = MutableMap()
  ): Unit = {
    c match {
      case Syntax.Declaration(id, args, ty, _) =>
        sym_ident(id)
        for (a <- args) {
          space()
          block { arg(a, block = false, notations) }
        }
        colon(); term(ty)
      case Syntax.DefableDecl(id, ty, _, _) =>
        write("def ")
        sym_ident(id)
        colon(); term(ty)
      case Syntax.Definition(id, args, ty, tm, _) =>
        write("def ")
        sym_ident(id)
        for (a <- args) {
          space()
          block { arg(a, block = false, notations) }
        }
        for (ty <- ty) { colon(); term(ty) }
        dfn(); term(tm)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("thm ")
        sym_ident(id)
        for (a <- args) {
          space()
          block { arg(a, block = false, notations) }
        }
        colon(); term(ty)
        dfn(); term(prf)
      case Syntax.Rewrite(vars, lhs, rhs) =>
        if (vars.nonEmpty) write("[" + vars.mkString(sep = ", ") + "] ")
        term(lhs)
        ar_rew(); term(rhs)
    }
    dot()
    nl()
  }

  def require(module: String): Unit = {
    write("#REQUIRE ")
    mod_ident(module)
    dot()
    nl()
  }

}
