/** Translation of Isabelle (proof)terms into the lambda-Pi calculus **/


package isabelle.dedukti

import isabelle.Export_Theory.{No_Syntax, Prefix}
import isabelle._

import scala.annotation.tailrec

object Prelude {

  // Object name translation, and module dependencies management

  /* An Isabelle object can be uniquely identify from its id (module
   name dot name) and its kind (class, type, const, etc.). */
  def full_name(id: String, kind: String): String = id + "/" + kind

  /* However, to keep the translated name as close as possible to the
   original name, we remove the module prefix and the kind if this is
   possible. */

  // map Isabelle full_name -> translated name
  var namesMap: Map[String, String] = Map()

  // set of translated names
  var namesSet: Set[String] = Set()

  // Dedukti or Lambdapi module names cannot contain dots
  def mod_name(m: String): String = m.replace(".", "_").replace("-", "_")

  // module of a translated name
  var moduleOf: Map[String, String] = Map()

  def module_of(id: String): String = {
    moduleOf get id match {
      case None => error("unknown name:" + id)
      case Some(m) => m
    }
  }

  // map module -> set of modules it depends on
  var depsOf: Map[String, Set[String]] = Map()

  def deps_of(m: String): Set[String] = {
    depsOf get m match {
      case None => Set()
      case Some(set) => set
    }
  }

  def add_dep(m: String) = {
    if (m != current_module)
      depsOf += (current_module -> (deps_of(current_module) + m))
  }

  // currently translated module
  var current_module: String = "STTfa"
  def set_current_module(m: String) = { current_module = m }

  // add a new mapping from an Isabelle full_name to its translation
  def add_name(id: String, kind: String, module0: String = current_module) : String = {
    //print("add_name " + full_name(id, kind) + " -> ")
    val (translated_id, module) = id match {
      case Pure_Thy.FUN => ("arr", "STTfa")
      case Pure_Thy.PROP => ("prop", "STTfa")
      case Pure_Thy.IMP => ("imp", "STTfa")
      case Pure_Thy.ALL => ("all", "STTfa")
      case id =>
        val cut = id.split("[.]", 2)
        val (prefix, radical) = if (cut.length == 1) ("", cut(0)) else (cut(0), cut(1))
        // because Dedukti does not accept names with dots
        var translated_id = radical.replace(".", "_")
        if (kind == "var") translated_id += "_"
        if (namesSet(translated_id)) translated_id += "_" + kind
        if (namesSet(translated_id)) translated_id = prefix + "_" + translated_id
        if (namesSet(translated_id)) error("duplicated name: " + translated_id)
        (translated_id, module0)
    }
    //println(module + "/" + translated_id)
    if (translated_id == "proof_159372") println("found it with id "+id+" and kind "+kind+" in "+module)
    namesMap += full_name(id, kind) -> translated_id
    namesSet += translated_id
    moduleOf += translated_id -> module
    translated_id
  }

  // translate an Isabelle full_name
  def get_name(id: String, kind: String, module: String = current_module): String = {
    namesMap get (full_name(id, kind)) match {
      case None => add_name(id, kind, module)
      case Some(s) => { add_dep(module_of(s)); s }
    }
  }

  /* kinds */

  def class_ident(a: String): String = get_name(a, Markup.CLASS)
  def  type_ident(a: String): String = get_name(a, Export_Theory.Kind.TYPE )
  def const_ident(a: String): String = get_name(a, Export_Theory.Kind.CONST)
  def axiom_ident(a: String): String = get_name(a, Markup.AXIOM)
  def   thm_ident(a: String): String = get_name(a, Export_Theory.Kind.THM  )
  def   var_ident(a: String): String = get_name(a, "var")

  def add_proof_ident(serial: Long, module: String = current_module): Unit = {
    namesMap get (full_name(f"proof_$serial", "")) match {
      case None => add_name(f"proof_$serial", "", module)
      case Some(s) =>
    }
  }

  def ref_proof_ident(serial: Long): String = get_name(f"proof_$serial", "")

  /* prologue proper */

  val typeId: String = const_ident("Set")
  val  etaId: String = const_ident("El")
  val  epsId: String = const_ident("Prf")

  val typeT: Syntax.Term = Syntax.Symb(typeId)
  val  etaT: Syntax.Term = Syntax.Symb( etaId)
  val  epsT: Syntax.Term = Syntax.Symb( epsId)

  val propId: String = type_ident(Pure_Thy.PROP)
  val  funId: String = type_ident(Pure_Thy.FUN)
  val  impId: String = const_ident(Pure_Thy.IMP)
  val  allId: String = const_ident(Pure_Thy.ALL)

  val typeD: Syntax.Command  = Syntax.Declaration(typeId, Nil, Syntax.TYPE)

  val  etaN: Syntax.Notation = Syntax.Prefix("η", 10)
  val  etaD: Syntax.Command  = Syntax.DefableDecl(etaId, Syntax.arrow(typeT, Syntax.TYPE), inj = true, not = Some(etaN))

  val epsN: Syntax.Notation = Syntax.Prefix("ε", 10)
  val epsTy: Syntax.Term = Syntax.arrow(Syntax.Appl(etaT, Syntax.Symb(propId)), Syntax.TYPE)
  val epsD: Syntax.Command = Syntax.DefableDecl(epsId, epsTy, not = Some(epsN))

  // Typing context (for implicit arguments)
  var global_types: Map[Syntax.Ident, Syntax.Typ] = Map(
    typeId -> Syntax.TYPE,
    etaId -> Syntax.arrow(typeT, Syntax.TYPE),
    epsId -> epsTy
  )

}

object Translate {
  import Prelude._
  var global_eta_expand = false


  /* binders */

  def bound_type_argument(name: String, impl: Boolean = false): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), typeT, impl)

  def bound_term_argument(name: String, ty: Term.Typ, impl: Boolean = false): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), eta(typ(ty)), impl)

  def bound_proof_argument(name: String, tm: Term.Term, bounds: Bounds): Syntax.BoundArg =
    Syntax.BoundArg(Some(var_ident(name)), eps(term(tm, bounds)))

  // Object to record de Bruijn index names
  sealed case class Bounds(
    trm: List[String] = Nil,
    prf: List[String] = Nil
  ) {
    def add_trm(tm: String): Bounds = copy(trm = tm :: trm)
    def add_prf(pf: String): Bounds = copy(prf = pf :: prf)

    def get_trm(idx: Int): String = trm(idx)
    def get_prf(idx: Int): String = prf(idx)
  }


  /* types and terms */

  def typ(ty: Term.Typ): Syntax.Typ =
    ty match {
      case Term.TFree(a, _) =>
        Syntax.Var(var_ident(a))
      case Term.Type(c, args) =>
        val id_c = type_ident(c)
        val impl = try implArgsMap(id_c) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(id_c), args.map(typ), impl)
      case Term.TVar(xi, _) => error("Illegal schematic type variable " + xi.toString)
    }

  def eta(ty: Syntax.Term): Syntax.Typ =
    Syntax.Appl(etaT, ty)

  def term(tm: Term.Term, bounds: Bounds): Syntax.Term =
    tm match {
      case Term.Const(c, typargs) =>
        val id_c = const_ident(c)
        val impl = try implArgsMap(id_c) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(id_c), typargs.map(typ), impl)
      case Term.Free(x, _) =>
        Syntax.Var(var_ident(x))
      case Term.Var(xi, _) => error("Illegal schematic variable " + xi.toString)
      case Term.Bound(i) =>
        try Syntax.Var(var_ident(bounds.get_trm(i)))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable " + i) }
      case Term.Abs(x, ty, b) =>
        Syntax.Abst(bound_term_argument(x, ty), term(b, bounds.add_trm(x)))
      case Term.OFCLASS(t, c) =>
        Syntax.Appl(Syntax.Symb(class_ident(c)), typ(t))
      case Term.App(a, b) =>
        Syntax.Appl(term(a, bounds), term(b, bounds))
    }

  def eps(tm: Syntax.Term): Syntax.Term =
    Syntax.Appl(epsT, tm)

  def proof(prf: Term.Proof, bounds: Bounds): Syntax.Term =
    prf match {
      case Term.PBound(i) =>
        try Syntax.Var(var_ident(bounds.get_prf(i)))
        catch { case _: IndexOutOfBoundsException => isabelle.error("Loose bound variable (proof) " + i) }
      case Term.Abst(x, ty, b) =>
        Syntax.Abst(bound_term_argument(x, ty), proof(b, bounds.add_trm(x)))
      case Term.AbsP(x, prf, b) =>
        Syntax.Abst(
          bound_proof_argument(x, prf, bounds),
          proof(b, bounds.add_prf(x)))
      case Term.Appt(a, b) =>
        Syntax.Appl(proof(a, bounds), term(b, bounds))
      case Term.AppP(a, b) =>
        Syntax.Appl(proof(a, bounds), proof(b, bounds))
      case axm: Term.PAxm =>
        val id = axiom_ident(axm.name)
        val impl = try implArgsMap(id) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(id), axm.types.map(typ), impl)
      case thm: Term.PThm =>
        val head = if (thm.name.nonEmpty) thm_ident(thm.name) else ref_proof_ident(thm.serial)
        val impl = try implArgsMap(head) catch { case _ : Throwable => Nil }
        Syntax.appls(Syntax.Symb(head), thm.types.map(typ), impl)
      case _ => error("Bad proof term encountered:\n" + prf)
    }


  /* eta contraction */

  // Looks if ident is used freely in term
  def lambda_contains(term: Syntax.Term, ident: Syntax.Ident): Boolean =
    term match {
      case Syntax.TYPE => false
      case Syntax.Symb(id) => id == ident
      case Syntax.Var(id)  => id == ident
      case Syntax.Appl(t1, t2, _) => lambda_contains(t1, ident) || lambda_contains(t2, ident)
      case Syntax.Abst(Syntax.BoundArg(arg, ty, _), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
      case Syntax.Prod(Syntax.BoundArg(arg, ty, _), t) =>
        !arg.contains(ident) && (lambda_contains(ty, ident) || lambda_contains(t, ident))
    }

  // Replace all free uses of ident to value in tm
  def lambda_replace(tm: Syntax.Term, ident: Syntax.Ident, value: Syntax.Term): Syntax.Term =
    tm match {
      case Syntax.TYPE => tm
      case Syntax.Symb(id) if id == ident => value
      case Syntax.Symb(_) => tm
      case Syntax.Var(id) if id == ident => value
      case Syntax.Var(_) => tm
      case Syntax.Appl(t1, t2, b) => Syntax.Appl(lambda_replace(t1, ident, value), lambda_replace(t2, ident, value), b)
      case Syntax.Abst(Syntax.BoundArg(arg, ty, b), t) =>
        Syntax.Abst(Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
      case Syntax.Prod(Syntax.BoundArg(arg, ty, b), t) =>
        Syntax.Prod(Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b),
          if (arg.fold(false)(arg => arg == ident)) t
          else lambda_replace(t, ident, value))
    }

  // Same as above
  def lambda_replace_arg(arg: Syntax.BoundArg, ident: Syntax.Ident, value: Syntax.Term): Syntax.BoundArg =
    arg match {
      case Syntax.BoundArg(arg, ty, b) =>
        Syntax.BoundArg(arg, lambda_replace(ty, ident, value), b)
    }

  // Contract λ(x: _), (Λ x)
  def eta_contract(tm: Syntax.Term) : Syntax.Term =
    tm match {
      case Syntax.Abst(Syntax.BoundArg(Some(id), ty, false), tm2) =>
        eta_contract(tm2) match {
          case Syntax.Appl(tm1, Syntax.Var(id2), _)
            if id == id2 && !lambda_contains(tm1, id) => eta_contract(tm1)
          case tm2 => Syntax.Abst(Syntax.BoundArg(Some(id), eta_contract(ty), implicit_arg = false), tm2)
        }

//      case Syntax.Prod(Syntax.BoundArg(Some(id), ty, false), tm2) =>
//        eta_contract(tm2) match {
//          case Syntax.Appl(tm1, Syntax.Var(id2), _)
//            if id == id2 && !lambda_contains(tm1, id) => eta_contract(tm1)
//          case tm2 => Syntax.Prod(Syntax.BoundArg(Some(id), eta_contract(ty), implicit_arg = false), tm2)
//        }

      case Syntax.Abst(Syntax.BoundArg(id, ty, impl), tm2) =>
        Syntax.Abst(Syntax.BoundArg(id, eta_contract(ty), impl), eta_contract(tm2))

      case Syntax.Prod(Syntax.BoundArg(id, ty, impl), tm2) =>
        Syntax.Prod(Syntax.BoundArg(id, eta_contract(ty), impl), eta_contract(tm2))

      case Syntax.Appl(t1, t2, impl) => Syntax.Appl(eta_contract(t1), eta_contract(t2), impl)
      case _ => tm
    }

  case class Mut[A](var value: A) {}

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

  // Escape default arguments
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

  // Create and name new arguments, only if the spine does not provide them
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
    val pure_args = args.map { case Syntax.BoundArg(Some(name), _, _) => Syntax.Var(name) }
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
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) }
        val abstracted = named_args.foldRight(applied)(Syntax.Abst.apply)
        abstracted

      case Syntax.Var(id) =>
        val named_args = name_args(ctxt(id), spine_args, ctxt, name_ref)
        val applied1 = expanded_args.foldLeft(head) { case (tm, (arg, impl)) => Syntax.Appl(tm, arg, impl) }
        val applied = named_args.foldLeft(applied1) { case (tm, Syntax.BoundArg(Some(name), _, impl)) => Syntax.Appl(tm, Syntax.Var(name), impl) }
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
  }

  var implArgsMap: Map[String, List[Boolean]] = Map()

  /* type classes */

  def class_decl(c: String): Syntax.Command = {
    val class_type = Syntax.arrow(typeT, Syntax.Appl(etaT, Syntax.Symb(propId)))
    val id_c = class_ident(c)
    implArgsMap  += id_c -> List(false)
    global_types += id_c -> class_type
    Syntax.Declaration(id_c, Nil, class_type)
  }


  /* types */

  def type_decl(c: String, args: List[String], rhs: Option[Term.Typ], not: Export_Theory.Syntax): Syntax.Command = {
    val full_ty = Syntax.arrows(List.fill(args.length)(typeT), typeT)
    val id_c = type_ident(c)
    implArgsMap  += id_c -> List.fill(args.length)(false)
    global_types += id_c -> full_ty

    rhs match {
      case None =>
        Syntax.Declaration(id_c, Nil, full_ty, notation_decl(not))
      case Some(rhs) => {
        val translated_rhs = typ(rhs)
        val full_tm : Syntax.Term = args.map(bound_type_argument(_)).foldRight(translated_rhs)(Syntax.Prod.apply)
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

  def const_decl(c: String, typargs: List[String], ty: Term.Typ, rhs: Option[Term.Term], not: Export_Theory.Syntax): Syntax.Command = {
    val id_c = const_ident(c)
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
