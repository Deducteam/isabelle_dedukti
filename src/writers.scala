/** Concrete syntax for various lambda-Pi implementations **/

package isabelle.dedukti

import isabelle.*
import isabelle.dedukti.Syntax.*

import java.io.{BufferedWriter, FileOutputStream, OutputStreamWriter, Writer}
import java.nio.file.{Files, StandardCopyOption}
import scala.collection.mutable.Map as MutableMap

/** Opens a path.part file for writing and then copy it to path.
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

/** Tools to write <span style="color:#9932CC;">Lambdapi</span> identifiers */
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

/** Tools for writing in a translated $dklp file
 *  <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference Dedukti (purple)
 *       $lp: reference Lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some Lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">Dedukti</span>
 * @define lp <span style="color:#9932CC;">Lambdapi</span>
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
  def write(c: Char): Unit = writer.write(c)

  def write(s: String): Unit = writer.write(s)

  def space(): Unit = write(' ')

  /** Write a newline character */
  def nl(): Unit = write('\n')

  /** Write a left parenthesis */
  def lpar(): Unit = write('(')

  /** Write a right parenthesis */
  def rpar(): Unit = write(')')

  def colon(): Unit = write(" : ")

  /** enclose the result of body inside parentheses */
  def block(body: => Unit): Unit = {
    lpar(); body; rpar()
  }

  /** To be used while in the middle of writing a term.
   * Does <$arg>body<$arge>, but may enclose the results inside parentheses depending
   * on priorities and associativity of notations. Can be used without notations (like in $dk)
   * by having a default notation for arrows for example
   *
   * @param curNot   the $lp notation of the current symbol
   * @param prevNot  the $lp notation of the previous symbol
   * @param right    used if <$arg>curNot<$arge> and <$arg>prevNot<$arge> are the same infix notation,
   *                 is true if we are on the right of the previous symbol.
   *                 Default: <code>false</code>
   * @param force_no input true to force non-parenthesising, for example when simply
   *                 writing one symbol. Default: <code>false</code>
   * @param body     a writing command
   */
  def block_if(
                curNot: Syntax.Notation,
                prevNot: Syntax.Notation,
                right: Boolean = false,
                force_no: Boolean = false)(
                body: => Unit
              ): Unit = {
    val prio1: Double = getPriority(curNot).getOrElse(isabelle.error("NotImplemented"))
    val prio2: Double = getPriority(prevNot).getOrElse(isabelle.error("NotImplemented"))

    val doBlock = curNot match {
      case _ if prio1 < prio2 => true
      case _ if prio1 > prio2 => false
      case _ if curNot != prevNot => true
      case Prefix(_, _) => true
      case Infix(_, _) => true
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
           prevNot: Notation = justHadPars, no_impl: Boolean = false,
           right: Boolean = false, needs_explicit: Boolean = false): Unit

  /** Write on <code>this</code> an argument and its type
   *
   * @param a         the $dklp argument to write
   * @param block     true if it needs to be parenthesised
   * @param notations a map between identifiers and their notation
   */
  def arg(a: Syntax.BoundArg, block: Boolean, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit

  def comment(c: String): Unit

  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit

  def require(module:String) : Unit
}

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference Dedukti (purple)
 *       $lp: reference Lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       $this: references the object itself (code)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some Lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">Dedukti</span>
 * @define lp <span style="color:#9932CC;">Lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define this <code>this</code>
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

  /** true if <$arg>ident<$arge> is non-empty and does not contain
   *  characters that require escaping for Lambdapi */
  def is_regular_identifier(ident: String): Boolean =
    ident.nonEmpty &&
      ident.forall(c => !" ,;\r\t\n(){}[]:.`\"".contains(c))

  /** Manually escape the name given to unnamed lambda abstraction arguments which doesn't
   *  fit Lambdapi's rules, even when escaping.
   */
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

  /** if <$arg>needs_explicit<$arge> is <code>true</code>, write an @ */
  def explicit(needs_explicit: Boolean): Unit = if (needs_explicit) write("@")
  /** prints <$str>";"<$stre> and goes to next line */
  def end_command() : Unit = { semicolon(); nl() }

  /** Write on $this a $lp term that is an application (can be a head only),
   *  pretty-prints infix operators.
   *
   * @param t the $lp term to write
   * @param notations a map between identifiers and their notation
   * @param prevNot the notation of the last symbol read
   * @param right whether the term to write is on the right of an infix operator
   */
  def appl(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation, no_impl: Boolean = false, right: Boolean, needs_explicit: Boolean = false): Unit = {
    val (head, pre_spine) = Syntax.destruct_appls(t)
    val spine = pre_spine.filter(!_._2).map(_._1)
    val contains_impl_arg = pre_spine.exists(_._2)
    val new_explicit = needs_explicit || contains_impl_arg
    head match {
      case Syntax.Symb(id) if notations contains id =>
        val not = notations(id)
        val op = getOperator(not)
        (not, spine) match {
          case (Syntax.Quantifier(_), _) => isabelle.error("NotImplemented")
          case (Syntax.Prefix(op, _), List(arg)) if !(no_impl && contains_impl_arg) =>
            block_if(not, prevNot, right){
              sym_qident(op)
              space()
              term(arg, notations, not, no_impl)
            }
          case (Syntax.Infix(_, _) | Syntax.InfixL(_, _) | Syntax.InfixR(_, _), List(arg1, arg2)) if !(no_impl && contains_impl_arg) =>
            block_if(not, prevNot, right){
              term(arg1, notations, not, no_impl)
              space()
              sym_qident(op)
              space()
              term(arg2, notations, not, no_impl, right = true)
            }
          case _ =>
            val not = Syntax.appNotation
            val force_no = pre_spine.isEmpty
            block_if(not, prevNot, right, force_no) {
              explicit(new_explicit)
              block(sym_qident(op))
              for ((arg, _) <- pre_spine) {
                space(); term(arg, notations, not, no_impl, right = true)
              }
            }
          }
      case _ =>
        val not = appNotation
        val force_no = pre_spine.isEmpty
        block_if(not, prevNot, right, force_no){
          term(head, notations, not, right, needs_explicit = new_explicit)
          for ((arg, _) <- pre_spine) {
            space()
            term(arg, notations, not, right = true)
          }
        }
    }
  }

  /** Particular case of <$met><u>[[term]]</u><$mete>. */
  def term_notation(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation, no_impl: Boolean, right: Boolean, needs_explicit: Boolean): Unit =
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) if notations contains id =>
        appl(t, notations, prevNot, no_impl, right, needs_explicit)
      case Syntax.Symb(id) =>
        explicit(needs_explicit)
        sym_qident(id)
      case Syntax.Var(id) =>
        var_ident(id)
      case Syntax.Appl(_, _, _) =>
        appl(t, notations, prevNot, no_impl, right, needs_explicit)
      case Syntax.Abst(a, t) =>
        val not = absNotation
        block_if(not, prevNot, right) {
          lambda(); arg(a, block = false, notations); comma(); term(t, notations, not, no_impl = no_impl, needs_explicit = needs_explicit)
        }
      case Syntax.Prod(Syntax.BoundArg(None, ty1, false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          term(ty1, notations, not, no_impl)
          arrow()
          term(ty2, notations, not, no_impl, right = true)
        }
      case Syntax.Prod(a, t) =>
        val not = absNotation
        block_if(not, prevNot, right) {
          pi(); arg(a, block = false, notations); comma(); term(t, notations, not, no_impl)
        }
    }

  /** Particular case of <$met><u>[[term]]</u><$mete>. */
  def term_no_notation(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
                       prevNot: Notation, no_impl: Boolean, right: Boolean, needs_explicit: Boolean): Unit =
    t match {
      case Syntax.TYPE =>
        write("TYPE")
      case Syntax.Symb(id) if notations contains id =>
        error("There should be no notations in this mode")
      case Syntax.Symb(id) =>
        explicit(needs_explicit)
        sym_qident(id)
      case Syntax.Var(id) =>
        var_ident(id)
      case Syntax.Appl(t1, t2, isImplicit) =>
        val not = appNotation
        block_if(not, prevNot, right) {
          term(t1, notations, not, needs_explicit = isImplicit || needs_explicit)
          space()
          term(t2, notations, not, right = true)
        }
      case Syntax.Abst(a, t) =>
        block_if(Syntax.absNotation, prevNot, right) {
          lambda(); arg(a, block = false, notations); comma(); term(t, notations, needs_explicit = needs_explicit)
        }
      case Syntax.Prod(Syntax.BoundArg(None, ty1, false), ty2) =>
        val not = arrNotation
        block_if(not, prevNot, right) {
          term(ty1, notations, not)
          arrow()
          term(ty2, notations, not, right = true)
        }
      case Syntax.Prod(a, t) =>
        val not = absNotation
        block_if(not, prevNot, right) {
          pi(); arg(a, block = false, notations); comma(); term(t, notations, not)
        }
    }

  /** Write on $this a $lp term
   *
   * @param t         the $lp term to write
   * @param notations a map between identifiers and their notation
   * @param prevNot   the notation of the last symbol read
   * @param right     whether the term to write is on the right of an infix operator
   */
  def term(t: Syntax.Term, notations: MutableMap[Syntax.Ident, Syntax.Notation],
           prevNot: Notation = justHadPars, no_impl: Boolean = false,
           right: Boolean = false, needs_explicit: Boolean = false): Unit =
    if (use_notations)
      term_notation(t, notations, prevNot, no_impl, right, needs_explicit)
    else
      term_no_notation(t, notations, prevNot, no_impl, right, needs_explicit)

  
  def arg(a: Syntax.BoundArg, block: Boolean, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    if (a.implicit_arg) write("[")
    else if (block) lpar()
    a.id match {
      case Some(id) => var_ident(id)
      case None => write('_')
    }
    colon()
    term(a.typ, notations)
    if (a.implicit_arg) write("]")
    else if (block) rpar()
  }

  /** comment + new line */
  def comment(c: String): Unit = {
    write("// " + c)
    nl()
  }

  /** Marks pattern variables in a term in a rewrite rule
   *
   *  @param t the $lp term in which to apply the changes,
   *           left or right-hand side of the rule
   *  @param vars the set of names of variables to mark
   *
   *  @return a copy of t in which <$str>'$'<$stre> is prepended to the name
   *          of all free variables with a name in <$arg>vars<$arge>
   */
  def patternize(t: Syntax.Term, vars: Set[Ident]): Syntax.Term = {
    def newvars(idopt: Option[Ident]): Set[Ident] = idopt.fold(vars)(vars - _)
    t match {
      case Syntax.TYPE => t
      case Syntax.Symb(_) => t
      case Syntax.Var(id) if vars(id) => Syntax.Var("$" + id)
      case Syntax.Var(_) => t
      case Syntax.Appl(t1, t2, b) => Syntax.Appl(patternize(t1, vars), patternize(t2, vars), b)
      case Syntax.Abst(BoundArg(idopt, ty, impl), t) =>
        Syntax.Abst(BoundArg(idopt, patternize(ty,vars), impl), patternize(t, newvars(idopt)))
      case Syntax.Prod(BoundArg(idopt, ty, impl), t) =>
        Syntax.Prod(BoundArg(idopt, patternize(ty,vars), impl), patternize(t, newvars(idopt)))
    }
  }

  /** Writes a $lp notation on $this */
  def notation(notation: Notation): Unit = {
    write ("notation ")
    notation match {
      case Prefix(op, priority) => sym_qident(op); space(); write("prefix");      space(); write(priority.toString)
      case Infix (op, priority) => sym_qident(op); space(); write("infix");       space(); write(priority.toString)
      case InfixL(op, priority) => sym_qident(op); space(); write("infix left");  space(); write(priority.toString)
      case InfixR(op, priority) => sym_qident(op); space(); write("infix right"); space(); write(priority.toString)
      case Quantifier(op) => sym_qident(op); space(); write("quantifier")
    }
  }

  /** Writes a $lp symbol definition and the corresponding notation on $this.
   *  Does not use/write the notation if variable <code>use_notations</code> is set to false.
   * 
   * @param id the (possibly modified) identifier of the symbol in $isa
   * @param args the list of arguments of the symbol
   * @param ty_opt the optional type of the symbol
   * @param body_opt the optional definition of the symbol
   * @param nota_opt the optional notation of the symbol
   * @param notations a map between identifiers and their $lp notation
   */
  def symbol_and_notation(id: Ident, args: List[BoundArg], ty_opt: Option[Typ], body_opt: Option[Term],
                          nota_opt: Option[Notation], notations: MutableMap[Ident, Notation]): Unit = {
    val (new_id, new_nota_opt) =
      if (use_notations) (nota_opt.fold(id)(getOperator), nota_opt)
      else (id, None)
    write("symbol ");
    sym_ident(new_id)
    for (a <- args) {
      space(); arg(a, block = true, notations)
    }
    for (ty <- ty_opt) {
      colon(); term(ty, notations)
    }
    for (tm <- body_opt) {
      colon_equal(); term(tm, notations)
    }
    for (not <- new_nota_opt) {
      end_command(); notation(not); notations(id) = not
    }
  }

  /** Writes the $lp command <$arg>c<$arge> on $this, possibly updating the
   *  <$arg>notations<$arge> map.
   */
  def command(c: Syntax.Command, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    c match {
      case Syntax.Rewrite(vars, lhs, rhs) =>
        val vars_set = Set.from(vars)
        write("rule ")
        term(patternize(lhs, vars_set), notations, no_impl = true)
        hook_arrow()
        term(patternize(rhs, vars_set), notations, no_impl = true)
      case Syntax.Declaration(id, args, ty, not) =>
        write("constant ")
        symbol_and_notation(id, args, Some(ty), None, not, notations)
      case Syntax.DefableDecl(id, ty, inj, not) =>
        if (inj) write("injective ")
        symbol_and_notation(id, List(), Some(ty), None, not, notations)
      case Syntax.Definition(id, args, ty, tm, not) =>
        symbol_and_notation(id, args, ty, Some(tm), not, notations)
      case Syntax.Theorem(id, args, ty, prf) =>
        write("opaque ")
        symbol_and_notation(id, args, Some(ty), Some(prf), None, notations)
    }
  end_command()
  }
  
  /** Writes on $this the $lp command to set the "eta_equality" flag on */
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
           prevNot: Notation = justHadPars, no_impl: Boolean = false,
           right: Boolean = false, needs_explicit: Boolean = false): Unit =
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
    
  def arg(a: Syntax.BoundArg, block: Boolean, notations: MutableMap[Syntax.Ident, Syntax.Notation]): Unit = {
    if (block) lpar()
    a.id match {
      case Some(id) => var_ident(id)
      case None => write('_')
    }
    colon()
    term(a.typ, notations)
    if (block) rpar()
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
