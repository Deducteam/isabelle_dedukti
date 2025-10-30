/** Translation of Isabelle (proof)terms into the lambda-Pi calculus **/


package isabelle.dedukti

import isabelle.Export_Theory.{No_Syntax, Prefix}
import isabelle._

import scala.collection.mutable
import scala.annotation.tailrec

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference dedukti (purple)
 *       $lp: reference lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define mete /span></code
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
object Prelude {
  
  def testmet:Unit = ()

  // Object name translation, and module dependencies management

  // An Isabelle object can be uniquely identified from its id (module
  // name dot name) and its kind (class, type, const, etc.).

  //The following scaladoc contains commands used throughout.
  /**
   * Making  an <span style="color:#FFFF00">Isabelle</span> object name unique by specifying its kind.
   * @param id $arg test$arge the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @return the string obtained by appending
   *         <code><span style="color:#FFC0CB;">kind</span></code>
   *         to <code><span style="color:#FFC0CB;">id</span></code>, with
   *         a slash to separate them
   */
  def full_name(id: String, kind: String): String = id + "/" + kind

  /* However, to keep the translated name as close as possible to the
   original name, we remove the module prefix and the kind if this is
   possible. */

  /** map $lp <span style="color:#FFFF00">Isabelle</span> full_name -> translated name */
  var namesMap: Map[String, String] = Map()

  /** set of translated names */
  var namesSet: Set[String] = Set()

  /** Replaces dots with underscore in a name, as dedukti does not accept
   * dots in a name.
   * @param m the name to modify
   * @return the name with each '.' replaced with '_' */
  def mod_name(m: String): String = m.replace(".", "_").replace("-", "_")

  /** map translated name -> module */
  var moduleOf: Map[String, String] = Map()

  /** Get the module of a translated name using map moduleOf
   * @param id the translated name
   * @return the module in which it is defined. <br>
   *         Prints an error if the name cannot be found. */
  def module_of(id: String): String = {
    moduleOf get id match {
      case None => error("unknown name:" + id)
      case Some(m) => m
    }
  }
  
  var current_module: String = "STTfa"
  var map_theory_session: Map[String, String] = Map("STTfa" -> "Pure")
  
  def set_current_module(m: String): Unit = { current_module = m }
  def set_theory_session(t: String, s: String): Unit = {map_theory_session += t -> s}
  
  /** The string "STTfa" */
  val STTfa: String = "STTfa"

  /** Add a new mapping from an <span style="color:#FFFF00">Isabelle</span> full_name to its translation.
   * @param id the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @param module0 the current <span style="color:#9932CC;">dk/lp</span> module
   * @return a unique translated id, after updating maps to account for it */
  def add_name(id: String, kind: String, module0: String) : String = {
    val (translated_id,module) = id match {
      case Pure_Thy.FUN => ("arr",STTfa)
      case Pure_Thy.PROP => ("prop",STTfa)
      case Pure_Thy.IMP => ("imp",STTfa)
      case Pure_Thy.ALL => ("all",STTfa)
      case id =>
        val cut = id.split("[.]", 2)
        val (prefix, radical) = if (cut.length == 1) ("", cut(0)) else (cut(0), cut(1))
        /** because Dedukti does not accept names with dots */
        var translated_id = radical.replace(".","_")
        if (kind == "var") translated_id += "_"
        if (namesSet(translated_id)) translated_id += "_" + kind
        if (namesSet(translated_id)) translated_id = prefix + "_" + translated_id
        if (namesSet(translated_id)) error("duplicated name: " + translated_id)
        (translated_id,module0)
    }
    namesMap += full_name(id, kind) -> translated_id
    namesSet += translated_id
    moduleOf += translated_id -> module
    //println("add_name "+full_name(id,kind)+" -> "+translated_id)
    translated_id
  }

  /** Get the translated name of an <span style="color:#FFFF00">Isabelle</span> object using map namesMap
   * @param id the qualified identifier of the object (modulename.name)
   * @param kind the kind of the object (class, type, const, etc.)
   * @return the translated name of the object. <br>
   *         Prints an error if the object cannot be found. */
  def get_name(id: String, kind: String ): String = {
    namesMap get (full_name(id, kind)) match {
      case None => error ("id '"+full_name(id,kind)+"' not found")
      case Some(s) => s
    }
  }

  /* kinds */
  /** <pre><code><span style="color:#FFA500;">add_class_ident</span>(<span style="color:#FFC0CB;">a</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#FFC0CB;">a</span>+<span style="color:#006400;">"_class"</span>, Export_Theory.Kind.CONST, <span style="color:#FFC0CB;">module</span>) */
  def add_class_ident(a: String, module: String): String = add_name(a+"_class", Export_Theory.Kind.CONST, module)
  /** <pre><code><span style="color:#FFA500;">add_type_ident</span>(<span style="color:#FFC0CB;">a</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#FFC0CB;">a</span>, Export_Theory.Kind.TYPE, <span style="color:#FFC0CB;">module</span>) */
  def add_type_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.TYPE, module)
  /** <pre><code><span style="color:#FFA500;">add_const_ident</span>(<span style="color:#FFC0CB;">a</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#FFC0CB;">a</span>, Export_Theory.Kind.CONST, <span style="color:#FFC0CB;">module</span>) */
  def add_const_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.CONST, module)
  /** <pre><code><span style="color:#FFA500;">add_axiom_ident</span>(<span style="color:#FFC0CB;">a</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#FFC0CB;">a</span>, Markup.AXIOM, <span style="color:#FFC0CB;">module</span>) */
  def add_axiom_ident(a: String, module: String): String = add_name(a, Markup.AXIOM, module)
  /** <pre><code><span style="color:#FFA500;">add_thm_ident</span>(<span style="color:#FFC0CB;">a</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#FFC0CB;">a</span>, Export_Theory.Kind.THM, <span style="color:#FFC0CB;">module</span>) */
  def add_thm_ident(a: String, module: String): String = add_name(a, Export_Theory.Kind.THM, module)
  /** <pre><code><span style="color:#FFA500;">add_proof_ident</span>(<span style="color:#FFC0CB;">serial</span>, <span style="color:#FFC0CB;">module</span>) =
   * <span style="color:#FFA500;"><u>[[add_name]]</u></span>(<span style="color:#006400;">f"proof_</span>$<span style="color:#FFC0CB;">serial</span><span style="color:#006400;">"</span>, <span style="color:#006400;">""</span>, <span style="color:#FFC0CB;">module</span>) */
  def add_proof_ident(serial: Long, module: String): String = add_name(f"proof_$serial", "", module)

  /** The translated name of an <span style="color:#FFFF00">Isabelle</span> class
   * @param a the name of the class
   * @return The translated name of the object
   *         <span style="color:#FFC0CB;">a</span>_class of kind const */
  def ref_class_ident(a: String): String = get_name(a+"_class", Export_Theory.Kind.CONST)
  /** The translated name of an <span style="color:#FFFF00">Isabelle</span> type
   *
   * @param a the name of the type
   * @return The translated name of the object
   *         <span style="color:#FFC0CB;">a</span> of kind type */
  def ref_type_ident(a: String): String = get_name(a, Export_Theory.Kind.TYPE )
  /** The translated name of an <span style="color:#FFFF00">Isabelle</span> constant
   *
   * @param a the name of the constant
   * @return The translated name of the object
   *         <span style="color:#FFC0CB;">a</span> of kind const */
  def ref_const_ident(a: String): String = get_name(a, Export_Theory.Kind.CONST)
  /** The translated name of an <span style="color:#FFFF00">Isabelle</span> axiom
   *
   * @param a the name of the axiom
   * @return The translated name of the object
   *         <span style="color:#FFC0CB;">a</span> of kind axiom */
  def ref_axiom_ident(a: String): String = get_name(a, Markup.AXIOM)
  /** The translated name of an <span style="color:#FFFF00">Isabelle</span> theorem
   *
   * @param a the name of the theorem
   * @return The translated name of the object
   *         <span style="color:#FFC0CB;">a</span> of kind thm */
  def ref_thm_ident(a: String): String = get_name(a, Export_Theory.Kind.THM)
  /** the name of the translation of an <span style="color:#FFFF00">Isabelle</span> proof step
   * @param serial the index of the proof step
   * @return The name that was assigned to it */
  def ref_proof_ident(serial: Long): String = get_name(f"proof_$serial", "")
  /** The translated name of a variable
   * @param a the name of the variable
   * @return The string <span style="color:#FFC0CB;">a</span><span>&#95;&#95</span>var */
  def var_ident(a: String): String = a+"__var"

  /* prologue proper */
  val typeId: String = add_const_ident("Set",STTfa)
  val  etaId: String = add_const_ident("El",STTfa)
  val  epsId: String = add_const_ident("Prf",STTfa)

  /** The <span style="color:#9932CC;">dk/lp</span> type
   * <code><span style="color:#87CEFA">Set</span></code> of simple types. */
  val typeT: Syntax.Term = Syntax.Symb(typeId)
  /** The <span style="color:#9932CC;">dk/lp</span> function
   * <code><span style="color:#87CEFA">El</span></code>
   * that maps a simple type to the type of its elements. */
  val  etaT: Syntax.Term = Syntax.Symb( etaId)
  /** The <span style="color:#9932CC;">dk/lp</span> function
   * <code><span style="color:#87CEFA">Prf</span></code> that maps
   * a simple type proposition to the type of its proofs. */
  val  epsT: Syntax.Term = Syntax.Symb( epsId)
  
  /** The name of the <span style="color:#9932CC;">dk/lp</span> simple type
   * <code><span style="color:#87CEFA">prop</span></code> of propositions. */
  val propId: String = add_type_ident(Pure_Thy.PROP,STTfa)
  /** The name of the <span style="color:#9932CC;">dk/lp</span> simple type constructor
   * <code><span style="color:#87CEFA">arr</span></code> representing arrow types. */
  val  funId: String = add_type_ident(Pure_Thy.FUN,STTfa)
  /** The name of the <span style="color:#9932CC;">dk/lp</span> simple type connector
   * <code><span style="color:#87CEFA">imp</span></code> representing implication. */
  val  impId: String = add_const_ident(Pure_Thy.IMP,STTfa)
  /** The name of the <span style="color:#9932CC;">dk/lp</span> simple type connector
   * <code><span style="color:#87CEFA">all</span></code> representing universal quantification. */
  val  allId: String = add_const_ident(Pure_Thy.ALL,STTfa)

  /** Declares the <span style="color:#9932CC;">dk/lp</span> type
   * <code><span style="color:#87CEFA">Set</span></code> of simple types. */
  val typeD: Syntax.Command  = Syntax.Declaration(typeId, Nil, Syntax.TYPE)

  val  etaN: Syntax.Notation = Syntax.Prefix("η", 10)
  /** Declares the <span style="color:#9932CC;">dk/lp</span> function
   * <code><span style="color:#87CEFA">El</span></code>
   * that maps a simple type to the type of its elements. */
  val  etaD: Syntax.Command  = Syntax.DefableDecl(etaId, Syntax.arrow(typeT, Syntax.TYPE), inj = true, not = Some(etaN))

  val epsN: Syntax.Notation = Syntax.Prefix("ε", 10)
  val epsTy: Syntax.Term = Syntax.arrow(Syntax.Appl(etaT, Syntax.Symb(propId)), Syntax.TYPE)
  /** Declares the <span style="color:#9932CC;">dk/lp</span> function
   * <code><span style="color:#87CEFA">Prf</span></code> that maps
   * a simple type proposition to the type of its proofs. */
  val epsD: Syntax.Command = Syntax.DefableDecl(epsId, epsTy, not = Some(epsN))

  // Tools for implicit arguments will be in comments in case they become usable again.
  
  // Typing context (for implicit arguments)
  /* var global_types: Map[Syntax.Ident, Syntax.Typ] = Map(
    typeId -> Syntax.TYPE,
    etaId -> Syntax.arrow(typeT, Syntax.TYPE),
    epsId -> epsTy
  ) */

}

object Translate {
  import Prelude.*
  var global_eta_expand = false


  /* binders */
  
  def bound_type_argument(name: String): Syntax.BoundArg = // += impl: Boolean = false
    Syntax.BoundArg(Some(var_ident(name)), typeT/*, impl*/)
  
  def bound_term_argument(name: String, ty: Term.Typ): Syntax.BoundArg = // += impl: Boolean = false
    Syntax.BoundArg(Some(var_ident(name)), eta(typ(ty))/*, impl*/)

  def bound_proof_argument(name: String, tm: Term.Term, bounds: Bounds): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), eps(term(tm, bounds)))

  /** Object used as a map between variable names and de Bruijn indices. <br>
   * Represents the context of bound variables. */
  sealed case class Bounds(
    trm: List[String] = Nil,
    prf: List[String] = Nil
  ) {
    /** Adds a mapping between a term variable and a de Bruijn index 
     * @param tm the name of the variable
     * @return the context updated with the new variable */
    def add_trm(tm: String): Bounds = copy(trm = tm :: trm)
    /** Adds a mapping between a proof variable and a de Bruijn index
     * @param tm the name of the variable
     * @return the context updated with the new variable */
    def add_prf(pf: String): Bounds = copy(prf = pf :: prf)

    /** Get a term variable from its de Bruijn index
     * @param idx the de Bruijn index of the variable
     * @return the name of the bound term variable at that index, fetched from a list. */
    def get_trm(idx: Int): String = trm(idx)
    /** Get a proof variable from its de Bruijn index
     *
     * @param idx the de Bruijn index of the variable
     * @return the name of the bound proof variable at that index, fetched from a list. */
    def get_prf(idx: Int): String = prf(idx)
  }


  /* types and terms */
  /** Translates an <span style="color:#FFFF00">Isabelle</span>
   * type to a <span style="color:#9932CC;">dk/lp</span> simple type 
   * @param ty the <span style="color:#FFFF00">Isabelle</span> type to translate
   * @return the corresponding <span style="color:#9932CC;">dk/lp</span> simple type */
  def typ(ty: Term.Typ): Syntax.Term =
    ty match {
      case Term.TFree(a, _) =>
        Syntax.Var(var_ident(a))
      case Term.Type(c, args) =>
        val id_c = ref_type_ident(c)
        //val impl = try implArgsMap(id_c) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(id_c), args.map(typ)/*, impl*/)
      case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
    }

  /** Function mapping a <span style="color:#9932CC;">dk/lp</span> simple type
   * to the type of its elements.
   * @param ty a <span style="color:#9932CC;">dk/lp</span> term,
   * which must be of type <code><span style="color:#87CEFA">Set</span></code>
   * in order for the output to be typable.
   * @return the type <code><span style="color:#87CEFA">El ty</span></code> of elements of
   * <code><span style="color:#FFC0CB;">ty</span></code> */
  def eta(ty: Syntax.Term): Syntax.Typ = Syntax.Appl(etaT, ty)

  /** Translates an <span style="color:#FFFF00">Isabelle</span>
   * term to a <span style="color:#9932CC;">dk/lp</span> one 
   *
   * @param tm the <span style="color:#FFFF00">Isabelle</span> term to translate
   * @param bounds the context of bound variables and their de Bruijn indices
   * @return the corresponding <span style="color:#9932CC;">dk/lp</span> term */
  def term(tm: Term.Term, bounds: Bounds): Syntax.Term =
    tm match {
      case Term.Const(c, typargs) =>
        val id_c = ref_const_ident(c)
        //val impl = try implArgsMap(id_c) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(id_c), typargs.map(typ)/*, impl*/)
      case Term.Free(x, _) =>
        Syntax.Var(var_ident(x))
      case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
      case Term.Bound(i) =>
        try Syntax.Var(var_ident(bounds.get_trm(i)))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
      case Term.Abs(x, ty, b) =>
        Syntax.Abst(bound_term_argument(x, ty), term(b, bounds.add_trm(x)))
      case Term.OFCLASS(t, c) =>
        Syntax.Appl(Syntax.Symb(ref_class_ident(c)), typ(t))
      case Term.App(a, b) =>
        Syntax.Appl(term(a, bounds), term(b, bounds))
    }

  /** Function mapping a <span style="color:#9932CC;">dk/lp</span> simple type proposition
   * to the type of its proofs.
   *
   * @param tm a <span style="color:#9932CC;">dk/lp</span> term,
   *           which must be of type <code><span style="color:#87CEFA">prop</span></code>
   *           in order for the output to be typable.
   * @return the type <code><span style="color:#87CEFA">Prf tm</span></code> of proofs of
   *         <code><span style="color:#FFC0CB;">tm</span></code> */
  def eps(tm: Syntax.Term): Syntax.Term =
    Syntax.Appl(epsT, tm)

  /** Translates an <span style="color:#FFFF00">Isabelle</span>
   * proof to a <span style="color:#9932CC;">dk/lp</span> term
   *
   * @param prf the <span style="color:#FFFF00">Isabelle</span> proof to translate
   * @param bounds the context of bound variables and their de Bruijn indices
   * @param cont an accumulator storing the result as a function (default: <code>t => t</code>) 
   * @return the corresponding <span style="color:#9932CC;">dk/lp</span> proof term */
  def proof(
    prf: Term.Proof,
    bounds: Bounds,
    cont: Syntax.Term => Syntax.Term = (t => t)/* continuation */
  ): Syntax.Term =
    prf match {
      case Term.PBound(i) =>
        try cont(Syntax.Var(var_ident(bounds.get_prf(i))))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i) }
      case Term.Abst(x, ty, b) =>
        proof(b, bounds.add_trm(x), prfb =>
          cont(Syntax.Abst(bound_term_argument(x, ty), prfb))
        )
      case Term.AbsP(x, prf, b) =>
        proof(b, bounds.add_prf(x), prfb =>
          cont(Syntax.Abst(bound_proof_argument(x, prf, bounds), prfb))
        )
      case Term.Appt(a, b) =>
        proof(a, bounds, prfa =>
          cont(Syntax.Appl(prfa, term(b, bounds)))
        )
      case Term.AppP(a, b) =>
        val prfa = proof(a, bounds)
        proof(b, bounds, prfb => cont(Syntax.Appl(prfa, prfb)))
      case axm: Term.PAxm =>
        val id = ref_axiom_ident(axm.name)
        //val impl = try implArgsMap(id) catch { case _ : Throwable => Nil }
        cont(Syntax.appls(Syntax.Symb(id), axm.types.map(typ)/*, impl*/))
      case thm: Term.PThm =>
        val head = if (!thm.thm_name.is_empty) ref_thm_ident(thm.thm_name.name) else {
          namesMap get (full_name("proof_"+thm.serial.toString, "")) match {
            case None => {
              // println("proof "+thm.serial+" is badly identified from theory "+thm.theory_name+thm.types.foldLeft(""){case (s,ty) => s+" "+ty.toString})
              add_proof_ident(thm.serial,current_module)
            }
            case Some(s) => 
              ref_proof_ident(thm.serial)
          }
        }
        val impl = try implArgsMap(head) catch { case _ : Throwable => Nil }
        cont(Syntax.appls(Syntax.Symb(head), thm.types.map(typ), impl))
      case _ => error("Bad proof term encountered:\n" + prf)
    }


  /* eta contraction */

  /** Looks if an identifier is used freely in a <span style="color:#9932CC;">dk/lp</span> term
   * @param term the term in which to search
   * @param ident the identifier to search for
   * @return true if a symbol or free variable named
   *         <code><span style="color:#FFC0CB;">ident</span></code>
   *         appears in <code><span style="color:#FFC0CB;">term</span></code>
   *         (including in the type of bound variables) */
  def lambda_contains(term: Syntax.Term, ident: Syntax.Ident): Boolean =
    term match {
      case Syntax.TYPE => false
      case Syntax.Symb(id) => id == ident
      case Syntax.Var(id)  => id == ident
      case Syntax.Appl(t1, t2/*, _*/) => lambda_contains(t1, ident) || lambda_contains(t2, ident)
      case Syntax.Abst(Syntax.BoundArg(arg, ty/*, _*/), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
      case Syntax.Prod(Syntax.BoundArg(arg, ty/*, _*/), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
    }

  /** Replaces all free occurrences of an identifier in a
   * <span style="color:#9932CC;">dk/lp</span> term with a term
   * @param tm the term in which to replace
   * @param ident the identifier to search for
   * @param value to term to replace all occurrences with
   * @return a copy of the term <code><span style="color:#FFC0CB;">tm</span></code>
   *         wherein any symbol or free variable named
   *         <code><span style="color:#FFC0CB;">ident</span></code> is replaced with
   *         <code><span style="color:#FFC0CB;">value</span></code>
   *         (including inside the type of bound variables) */
  def lambda_replace(tm: Syntax.Term, ident: Syntax.Ident, value: Syntax.Term): Syntax.Term =
    tm match {
      case Syntax.TYPE => tm
      case Syntax.Symb(id) => if (id == ident) value else tm
      case Syntax.Var(id) => if (id == ident) value else tm
      case Syntax.Appl(t1, t2/*, b*/) => Syntax.Appl(lambda_replace(t1, ident, value), lambda_replace(t2, ident, value), b)
      case Syntax.Abst(Syntax.BoundArg(arg, ty/*, b*/), t) =>
        Syntax.Abst(Syntax.BoundArg(arg, lambda_replace(ty, ident, value)/*, b*/),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
      case Syntax.Prod(Syntax.BoundArg(arg, ty/*, b*/), t) =>
        Syntax.Prod(Syntax.BoundArg(arg, lambda_replace(ty, ident, value)/*, b*/),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
    }

  /**  applies [[lambda_replace]] in the type of <span style="color:#FFC0CB;">arg</span>*/
  def lambda_replace_arg(arg: Syntax.BoundArg, ident: Syntax.Ident, value: Syntax.Term): Syntax.BoundArg =
    arg match {
      case Syntax.BoundArg(arg, ty/*, b*/) =>
        Syntax.BoundArg(arg, lambda_replace(ty, ident, value)/*, b*/)
    }

  /** Applies eta-contraction inside all subterms of a
   * <span style="color:#9932CC;">dk/lp</span> term.
   * @param tm the <span style="color:#9932CC;">dk/lp</span> term
   *           in which to do the contraction
   * @return a copy of <code><span style="color:#FFC0CB;">tm</span></code>
   *         in which all subterms of the form
   *         <code><span style="color:#87CEFA">λ x, t x </span></code>
   *         are replaced by t as long as x does not appear in t.*/
  def eta_contract(tm: Syntax.Term) : Syntax.Term =
    tm match {
      case Syntax.Abst(Syntax.BoundArg(Some(id), ty/*, false*/), tm2) =>
        eta_contract(tm2) match {
          case Syntax.Appl(tm1, Syntax.Var(id2)/*, _*/)
            if id == id2 && !lambda_contains(tm1, id) => eta_contract(tm1)
          case tm2 => Syntax.Abst(Syntax.BoundArg(Some(id), eta_contract(ty)/*, implicit_arg = false*/), tm2)
        }

      case Syntax.Abst(Syntax.BoundArg(id, ty/*, impl*/), tm2) =>
        Syntax.Abst(Syntax.BoundArg(id, eta_contract(ty)/*, impl*/), eta_contract(tm2))

      case Syntax.Prod(Syntax.BoundArg(id, ty/*, impl*/), tm2) =>
        Syntax.Prod(Syntax.BoundArg(id, eta_contract(ty)/*, impl*/), eta_contract(tm2))

      case Syntax.Appl(t1, t2/*, impl*/) => Syntax.Appl(eta_contract(t1), eta_contract(t2)/*, impl*/)
      case _ => tm
    }

  /** Mutable objects of type A. <br>
  * Simply contains a variable
  * <code><span style="color:#FFC0CB;">value</span></code> of type A. */
  case class Mut[A](var value: A) {}

  /** Basically implements some counter in an alphabetic string
   * representing a base 26 integer, stopping when it reaches only 'z's by replacing
   * <span style="color:#006400;">"zz....z"</span> with <span style="color:#006400;">"€aa....a"</span>*/
  def update_name(name: String): String = {
    if (!(name.length > 1 && name(0) == '€'))
      error("Broke invariant: " + name)
    var last_non_z = name.length - 1
    while (name(last_non_z) == 'z') {
      last_non_z -= 1
    }
    if (last_non_z == 0) {
      "€" + "a".repeat(name.length)
    } else {
      name.substring(0, last_non_z) + (name(last_non_z).toInt + 1).toChar.toString + "a".repeat(name.length - 1 - last_non_z)
    }
  }

  /** Given a <span style="color:#9932CC;">dk/lp</span> type and a list of bound arguments it depends on,
   * renames all named arguments by adding a <span style="color:#006400;">'£'</span> in front
   * @param argnames the list of bound arguments to rename, where the type of an argument might depend on the
   *                 arguments before it in the list.
   * @param ret_ty the return type parametrized by <code><span style="color:#FFC0CB;">argname</span></code>
   * @return the updated list and type, where all named variables are prefixed by a
   *         <span style="color:#006400;">'£'</span> and are replaced as such in the type of all arguments
   *         coming after in the list as well as in <code><span style="color:#FFC0CB;">ret_ty</span></code> */
  def alpha_escape(argnames: List[Syntax.BoundArg], ret_ty: Syntax.Typ) : (List[Syntax.BoundArg], Syntax.Typ) =
    argnames match {
      case Nil => (Nil, ret_ty)
      case (arg @ Syntax.BoundArg(None, ty, impl)) :: tl => {
        val (lst, new_ret_ty) = alpha_escape(tl, ret_ty)
        (arg :: lst, new_ret_ty)
      }
      case Syntax.BoundArg(Some(name), ty, impl) :: tl => {
        val new_name = "£" + name
        val (lst, new_ret_ty) = alpha_escape(tl.map(lambda_replace_arg(_, name, Syntax.Var(new_name))), lambda_replace(ret_ty, name, Syntax.Var(new_name)))
        (Syntax.BoundArg(Some(new_name), ty, impl) :: lst, new_ret_ty)
      }
    }

  /** <b>TODO: is it used for proofs? if not, then known_argnames is only used for type names</b><br>
   * Create and name new arguments to a <span style="color:#9932CC;">dk/lp</span>
   * function when they don't already exist (partially applied function)
   * @param known_argnames the names given to the arguments in the type (in case of a product and not an arrow type).
   *                       Supposed to be renamed using [[alpha_escape]] before being given to the function
   * @param spine The arguments already given to the function
   * @param ctxt a map storing the type of all bound variable in the context
   * @param name_ref
   * @see [[eta_expand]] */
  def name_args_of_list(known_argnames: List[Syntax.BoundArg], spine: List[Syntax.Term], ctxt: Map[String, Syntax.Typ], name_ref: Mut[String], ret_type: Syntax.Typ) : List[Syntax.BoundArg] = {
    (known_argnames, spine) match {
      case (Syntax.BoundArg(id, _, _) :: tl, tm :: spine) => {
        val real_id = id.getOrElse("")
        val replaced = tl.map(lambda_replace_arg(_, real_id, tm))
        name_args_of_list(replaced, spine, ctxt, name_ref, lambda_replace(ret_type, real_id, tm))
      }
      case (Syntax.BoundArg(Some(name), ty, impl) :: tl, Nil) => {
        val exp_ty = eta_expand(ty, ctxt, Mut(name_ref.value))
        val res = Syntax.BoundArg(Some(name), exp_ty, impl)
        if (name(0) != '£') error("Invariant broken")
        res :: name_args_of_list(tl, Nil, ctxt + (name -> exp_ty), name_ref, ret_type)
      }
      case (Syntax.BoundArg(None, ty, impl) :: tl, Nil) => {
        val name = name_ref.value
        val exp_ty = eta_expand(ty, ctxt, Mut(name))
        val res = Syntax.BoundArg(Some(name), exp_ty, impl)
        name_ref.value = update_name(name)
        res :: name_args_of_list(tl, Nil, ctxt + (name -> exp_ty), name_ref, ret_type)
      }
      case (Nil, sp) => name_args(ret_type, spine, ctxt, name_ref)
    }
  }

  def name_args(ty: Syntax.Typ, spine: List[Syntax.Term], ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]) : List[Syntax.BoundArg] =
    fetch_head_args_type(ty) match {
      case (Nil, _) => Nil
      case (lst, ty) => {
        val (argnames, ret_ty) = alpha_escape(lst, ty)
        name_args_of_list(argnames, spine, ctxt, name_ref, ret_ty)
      }
    }

  // Apply a list of arguments, given as lambda arguments
  def appls_args(tm: Syntax.Term, args: List[Syntax.BoundArg]): Syntax.Term = {
    val pure_args = args.map { case Syntax.BoundArg(Some(name), _, _) => Syntax.Var(name) case _ => error("oops") }
    val impl_list = args.map { case Syntax.BoundArg(_, _, impl) => impl }
    Syntax.appls(tm, pure_args, impl_list)
  }


  // Drop the first abstractions when there are arguments already, also replacing the abst argname with the argument proper
  // Does not handle it when some abst argname and some arguments share free idents
  // @tailrec
  // def drop(lst: List[Syntax.BoundArg], spine: List[Syntax.Term]): List[Syntax.BoundArg] =
  //   (lst, spine) match {
  //     case (Syntax.BoundArg(id, _, _) :: lst, tm :: spine) =>
  //       val real_id = id.getOrElse("")
  //       val replaced = lst.map(lambda_replace_arg(_, real_id, tm))
  //       drop(replaced, spine)
  //     case (lst, Nil) => lst
  //     case (Nil, _ :: _) => Nil
  //   }


  // Given an application, expand the head so that all the arguments are made clear, not just the ones present at the time
  def eta_expand_appl(t: Syntax.Term, ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]): Syntax.Term = {
    val (head, spine) = Syntax.destruct_appls(t)
    val expanded_args = spine.map { case (arg, impl) => (eta_expand(arg, ctxt, Mut(name_ref.value)), impl) }
    val spine_args = expanded_args.map(_._1)
    head match {
      case Syntax.Symb(id) =>
        val named_args = name_args(global_types(id), spine_args, ctxt, name_ref)
        val applied1 = expanded_args.foldLeft(head) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) case _ => error("oops") }
        val abstracted = named_args.foldRight(applied)(Syntax.Abst.apply)
        abstracted

      case Syntax.Var(id) =>
        val named_args = name_args(ctxt(id), spine_args, ctxt, name_ref)
        val applied1 = expanded_args.foldLeft(head) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) case _ => error("oops") }
        val abstracted = named_args.foldRight(applied)(Syntax.Abst.apply)
        abstracted

      case _ =>
        expanded_args.foldLeft(eta_expand(head, ctxt, name_ref)) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
    }
  }

  // Expand all idents which have a function type, so that the number of arguments they accept is made clear
  def eta_expand(tm: Syntax.Term, ctxt: Map[String, Syntax.Typ], name_ref: Mut[String]): Syntax.Term = {
    tm match {
      case Syntax.TYPE =>
        tm

      case Syntax.Symb(_) | Syntax.Var(_) | Syntax.Appl(_, _, _) =>
        eta_expand_appl(tm, ctxt, name_ref)

      case Syntax.Abst(Syntax.BoundArg(Some(name), ty, impl), t) =>
        Syntax.Abst(Syntax.BoundArg(Some(name), eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt + (name -> ty), name_ref))

      case Syntax.Abst(Syntax.BoundArg(None, ty, impl), t) =>
        Syntax.Abst(Syntax.BoundArg(None, eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt, name_ref))

      case Syntax.Prod(Syntax.BoundArg(Some(name), ty, impl), t) =>
        Syntax.Prod(Syntax.BoundArg(Some(name), eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt + (name -> ty), name_ref))

      case Syntax.Prod(Syntax.BoundArg(None, ty, impl), t) =>
        Syntax.Prod(Syntax.BoundArg(None, eta_expand(ty, ctxt, Mut(name_ref.value)), impl), eta_expand(t, ctxt, name_ref))
    }
  }
  def eta_expand(tm: Syntax.Term) : Syntax.Term = {
    if (global_eta_expand) eta_expand(tm, Map(), Mut("€a")) else tm
  }

  // Return if the abstraction argument and the product argument can be unified as a declaration argument
  def compatible_bound_args(ba1: Syntax.BoundArg, ba2: Syntax.BoundArg): Boolean =
    (ba1, ba2) match {
      case (Syntax.BoundArg(id1, ty1, impl1), Syntax.BoundArg(id2, ty2, impl2)) =>
        val id = (id1, id2) match {
          case (Some(a), Some(b)) => a == b
          case (None, Some(_)) => false
          case _ => true
        }
        id && ty1 == ty2 && impl1 == impl2
    }

  // Pop all compatible {abstraction, product} arguments and return their list and the remaining terms
  def fetch_head_args(tm: Syntax.Term, ty: Syntax.Term) : (List[Syntax.BoundArg], Syntax.Term, Syntax.Term) =
    (tm, ty) match {
      case (Syntax.Abst(arg @ Syntax.BoundArg(_, arg_ty, false), tm0),
        Syntax.Appl(Syntax.Symb("eta"), Syntax.Appl(Syntax.Appl(Syntax.Symb("fun"), arg_ty2, false), ret_ty, false), false))
      if arg_ty == eta(arg_ty2) => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, eta(ret_ty))
        (arg :: lst, tm1, ty1)
      }
      case (Syntax.Abst(arg @ Syntax.BoundArg(_, arg_ty, false), tm0),
        Syntax.Appl(Syntax.Symb("eps"), Syntax.Appl(Syntax.Appl(Syntax.Symb("imp"), arg_ty2, false), ret_ty, false), false))
      if arg_ty == eps(arg_ty2) => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, eps(ret_ty))
        (arg :: lst, tm1, ty1)
      }
      case (Syntax.Abst(arg, tm0), Syntax.Prod(arg2, ty0))
        if compatible_bound_args(arg, arg2) => {
        val (lst, tm1, ty1) = fetch_head_args(tm0, ty0)
        (arg :: lst, tm1, ty1)
      }

      case _ => (Nil, tm, ty)
  }

  // Pop all product arguments and return their list and the remaining term
  def fetch_head_args_type(ty: Syntax.Typ) : (List[Syntax.BoundArg], Syntax.Typ) =
    ty match {
      case Syntax.Appl(Syntax.Symb("eta"), Syntax.Appl(Syntax.Appl(Syntax.Symb("fun"), arg_ty, false), ret_ty, false), false) => {
        val (lst, ty1) = fetch_head_args_type(eta(ret_ty))
        (Syntax.BoundArg(None, eta(arg_ty)) :: lst, ty1)
      }
      case Syntax.Appl(Syntax.Symb("eps"), Syntax.Appl(Syntax.Appl(Syntax.Symb("imp"), arg_ty, false), ret_ty, false), false) => {
        val (lst, ty1) = fetch_head_args_type(eps(ret_ty))
        (Syntax.BoundArg(None, eps(arg_ty)) :: lst, ty1)
      }
      case Syntax.Prod(arg, ret_ty) => {
        val (lst, ty1) = fetch_head_args_type(ret_ty)
        (arg :: lst, ty1)
      }

      case _ => (Nil, ty)
    }

  /* notation */

  var notationsSet: Set[String] = Set()

  // Make sure that there are no two notations with the same op string
  // You can edit them here (eg. replace ≡ with ⩵ or _ with __ to avoid their escaping)
  def notations_get(op: String) : String = {
    var op1 = Symbol.decode(op)
    if (op1 == "≡") op1 = "⩵"
    while (notationsSet(op1)) {
      op1 = "~"+op1
    }
    notationsSet += op1
    op1
  }

  def notation_decl: Export_Theory.Syntax => Option[Syntax.Notation] = { // TODO: Ugly
    case No_Syntax => None
    case Prefix(op) => Some(Syntax.Prefix(notations_get(op), Syntax.defaultPrefixPriority))
    case Export_Theory.Infix(Export_Theory.Assoc.NO_ASSOC,    op, priority) => Some(Syntax.Infix (notations_get(op), priority))
    case Export_Theory.Infix(Export_Theory.Assoc.LEFT_ASSOC,  op, priority) => Some(Syntax.InfixL(notations_get(op), priority))
    case Export_Theory.Infix(Export_Theory.Assoc.RIGHT_ASSOC, op, priority) => Some(Syntax.InfixR(notations_get(op), priority))
    case _ => error("oops")
  }

  var implArgsMap: Map[String, List[Boolean]] = Map()

  /* type classes */

  def class_decl(module: String, c: String, d: Option[Term.Term]): Syntax.Command = {
    val out_type = eta(Syntax.Symb(propId))
    val class_type = Syntax.arrow(typeT,out_type)
    val id_c = add_class_ident(c,module)
    implArgsMap  += id_c -> List(false)
    global_types += id_c -> class_type
    d match {
      case None => Syntax.Declaration(id_c,List(),class_type)
      case Some(d) =>
        val typ_arg = Syntax.BoundArg(Some(var_ident("'a")),typeT)
        Syntax.Definition(id_c,List(typ_arg),Some(out_type),term(d,Bounds()),None)
    }
  }

  /* types */

  def type_decl(module: String, c: String, args: List[String], rhs: Option[Term.Typ], not: Export_Theory.Syntax): Syntax.Command = {
    val full_ty = Syntax.arrows(List.fill(args.length)(typeT), typeT)
    val id_c = add_type_ident(c,module)
    implArgsMap  += id_c -> List.fill(args.length)(false)
    global_types += id_c -> full_ty

    rhs match {
      case None =>
        Syntax.Declaration(id_c, Nil, full_ty, notation_decl(not))
      case Some(rhs) => {
        val translated_rhs = typ(rhs)
        val full_tm : Syntax.Term = args.map(bound_type_argument(_)).foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, ty) = fetch_head_args(eta_expand(eta_contract(full_tm)), full_ty)
        Syntax.Definition(id_c, new_args, Some(ty), contracted, notation_decl(not))
      }
    }
  }


  /* consts */

  def type_contains_arg(ty: Term.Typ, arg: String): Boolean =
    ty match {
      case Term.TFree(name, _) => name == arg
      case Term.Type(_, args) => args.exists(type_contains_arg(_, arg))
      case Term.TVar(_, _) => error("False assertion")
    }

  @tailrec
  def type_contains_arg_as_arg(ty: Term.Typ, arg: String): Boolean =
    ty match {
      case Term.Type(Pure_Thy.FUN, List(arg1, arg2)) => type_contains_arg(arg1, arg) || type_contains_arg_as_arg(arg2, arg)
      case Term.Type(_, _) => false  // Can maybe be more intelligent
      case Term.TFree(_, _) => false
      case Term.TVar(_, _) => error("False assertion")
    }

  def const_implicit_args(typargs: List[String], ty: Term.Typ): List[Boolean] = {
    var canStillBeImplicit = true  // No implicit arg after a non-implicit one
    typargs.map(arg => {
      canStillBeImplicit &&= type_contains_arg_as_arg(ty, arg)
      canStillBeImplicit
    })
  }

  def bound_type_arguments(args: List[String], impl: List[Boolean]): List[Syntax.BoundArg] =
    (args, impl) match {
      case (Nil, Nil) => Nil
      case (arg :: args, impl :: impls) => bound_type_argument(arg, impl) :: bound_type_arguments(args, impls)
      case (Nil, _) => isabelle.error("Implicit list too long.")
      case (_, Nil) => isabelle.error("Implicit list too short.")
    }

  def const_decl(module: String, c: String, typargs: List[String], ty: Term.Typ, rhs: Option[Term.Term], not: Export_Theory.Syntax): Syntax.Command = {
    val id_c = add_const_ident(c,module)
    val impl = const_implicit_args(typargs, ty)
    implArgsMap += id_c -> impl
    val bound_args = bound_type_arguments(typargs, impl)
    val full_ty = bound_args.foldRight(eta(typ(ty)))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))
    global_types += id_c -> contracted_ty
    rhs match {
      case None =>
        val (new_args, final_ty) = (Nil, contracted_ty) // fetch_head_args_type(contracted_ty)
        Syntax.Declaration(id_c, new_args, final_ty, notation_decl(not))
      case Some(rhs) => {
        val translated_rhs = term(rhs, Bounds())
        val full_tm = bound_args.foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, final_ty) = fetch_head_args(eta_expand(eta_contract(full_tm)), contracted_ty)
        Syntax.Definition(id_c, new_args, Some(final_ty), contracted, notation_decl(not))
      }
    }
  }

  /* theorems and proof terms */

  def stmt_decl(s: String, prop: Export_Theory.Prop, prf_opt: Option[Term.Proof]): Syntax.Command = {
    val args =
      prop.typargs.map(_._1).map(bound_type_argument(_)) :::
      prop.args.map(arg => bound_term_argument(arg._1, arg._2))

    val full_ty = args.foldRight(eps(term(prop.term, Bounds())))(Syntax.Prod.apply)
    val contracted_ty = eta_expand(eta_contract(full_ty))

    implArgsMap  += s -> List.fill(prop.typargs.length)(false) // Only those are applied immediately
    global_types += s -> contracted_ty

    try prf_opt match {
      case None => {
        val (new_args, final_ty) = (Nil, contracted_ty) // fetch_head_args_type(contracted_ty)
        //dfn_of_eq_decl(s, new_args, final_ty)++
        Syntax.Declaration(s, new_args, final_ty)
        }
      case Some(prf) => {
        val translated_rhs = proof(prf, Bounds())
        val full_prf : Syntax.Term = args.foldRight(translated_rhs)(Syntax.Abst.apply)
        val (new_args, contracted, final_ty) = fetch_head_args(eta_expand(eta_contract(full_prf)), contracted_ty)
        Syntax.Theorem(s, new_args, final_ty, contracted)
      }
    }
    catch { case e : Throwable => e.printStackTrace
      error("oops in " + quote(s)) }
//    catch { case ERROR(msg) => error(msg + "\nin " + quote(s)) }
  }

}
