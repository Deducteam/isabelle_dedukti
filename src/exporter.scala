/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle.*
import isabelle.Term.{Const as Cst, Proof as Prf, *}
import isabelle.Export_Theory.*

import java.io.*
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.control.Breaks.*

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
 *       <$isac>code<$isace>: some isabelle code (red,code)
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
 * @define isac code><span style="color:#D40606"
 * @define isace /span></code
 */
object Exporter {

  /** Compute the biggest theorem serial occurring in
   *  the proof of an $isa theorem. */
  def max_serial(thm: Entity[Thm]): Long = {
    def aux(p:Prf) : Long = p match {
      case PThm(serial,_,_,_) => serial
      case Appt(p,_) => aux(p)
      case AppP(p,q) => Math.max(aux(p), aux(q))
      case Abst(_,_,b) => aux(b)
      case AbsP(_,_,b) => aux(b)
      case _ => 0
    }
    aux(thm.the_content.proof)
  }

  /** Recursively splits an $isa term between its head and its arguments.
   * 
   * @param t the term being split
   * @param args the list of arguments encountered so far (default: <$met>Nil<$mete>)
   *             
   * @return the couple of the head function and the list of arguments it is applied to
   *         
   * @see <$met><u>[[isabelle.dedukti.Syntax.destruct_appls]]</u><$mete> for $dklp terms
   */
  @tailrec
  def head_args(t:Term, args:List[Term]=List()): (Term,List[Term]) = {
    t match {
      case App(u,v) => head_args(u,v::args)
      case _ => (t,args)
    }
  }

  /** True if the $isa term <$arg>t<$arge> is a free term variable or <$isac>Pure.type<$isace> */
  def is_Free_or_TYPE(t:Term): Boolean = {
    t match {
      case Free(_,_) => true
      case Term.Const(Pure_Thy.TYPE, List(TFree("'a"))) => true
      case _ => false
    }
  }

  /** tell if an $isa type is a free variable */
  def is_TFree(t:Typ): Boolean = {
    t match {
      case TFree(_,_) => true
      case _ => false
    }
  }

  /** Replace all free variables in an $isa term by De Bruijn indices (therefore binding them)
   * 
   *  @param revargs the list of bound variables, to which those bound in the term are added
   *         during the process. */
  def debruijn(revargs:List[Term], t:Term): Term = {
    t match {
      case Free(_,_) => Bound(revargs.indexOf(t))
      case App(u,v) => App(debruijn(revargs,u),debruijn(revargs,v))
      case Abs(n,ty,b) => Abs(n,ty,debruijn(Free(n,ty)::revargs,b))
      case _ => t
    }
  }

  /** build an $isa abstraction assuming that <$arg>arg<$arge> is a free variable */
  def abs(b:Term, arg:Term): Term = {
    arg match {
      case Free(n,ty) => Abs(n,ty,b)
      case _ => error("exporter.abs: not a free variable "+arg.toString)
    }
  }

  /** Reads an $isa session and possibly translates it to $dk files
   * 
   * @param options $isa options to read the session
   * @param session the $isa session to read
   * @param parent the parent session unless it is Pure
   * @param theory_graph the dependency graph of the theories in the session
   * @param translate whether to translate this theory or (if it is already translated for example)
   *                  to just read it to update name maps
   * @param dirs directories in which to find $lp dependencies
   * @param outdir the directory in which to translate (only useful if translate is <code>true</code>)
   */
  def exporter(
    options: Options,
    session: String,
    parent: Option[String],
    theory_graph: Document.Node.Name.Graph[Unit],
    translate: Boolean,
    term_cache: Term.Cache = Term.Cache.make(),
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    verbose: Boolean = false,
    outdir: String = "",
  ): Unit = {

    /** from an $isa equality axiom <$isac>Pure.eq[eqtys] lhs rhs<$isace>
     * where <code>lhs = <$isac>c[tys] x1 .. xn<$isace></code> with tys and xj variables,
     * returns <code>(c,dfn,eqtys,lhs)</code> where
     * <code>dfn=<$isac>λ x1...λ xn. rhs<$isace></code> 
     * 
     * @define isa <span style="color:#FFFF00">Isabelle</span>
     * @define isac code><span style="color:#D40606"
     * @define isace /span></code*/
    def is_eq_axiom(a:Entity[Axiom]): Option[(String,Term,List[Typ],Term)] = {
      if (!(a.name.endsWith("_def") || a.name.endsWith("_def_raw"))) None
      else a.the_content.prop.term match {
        case App(App(Cst(id, _), _), _) if id != "Pure.eq" =>
          if (verbose) progress.echo("axiom " + a.name + ": cannot extract definition because it is headed by " + id + " instead of Pure.eq")
          None
        case App(App(Cst(id, eqtys), lhs), rhs) =>
          head_args(lhs) match {
            case (Cst(n, tys), args) if !(tys.forall(is_TFree) && args.forall(is_Free_or_TYPE)) =>
              if (verbose) progress.echo("axiom " + a.name + ": cannot extract definition because it is not applied to free variables\n  axiom: " + a.the_content.prop.term.toString + "\n  type arguments: " + tys.toString + "\n  term arguments: " + args.toString)
              None
            case (Cst(n, tys), args) =>
              if (verbose) progress.echo("  head: " + h.toString + "\n  args: " + args.toString + "\n  rhs: " + rhs.toString)
              /* TODO: Modified this method quite a bit, especially here, please tell me if it is wrong
                 I particularly removed a part that I believe was impossible to reach. */
              if (args = List(Term.Const(Pure_Thy.TYPE, List(TFree(x, Nil))))) None
              else {
                val revargs = args.reverse
                val rhs2 = debruijn(revargs, rhs)
                val dfn = revargs.foldLeft(rhs2)(abs)
                Some(n, dfn, eqtys, lhs)
              }
            case _ => None
          }
        case _ => None
      }
    } 
    
    val notations: mutable.Map[Syntax.Ident, Syntax.Notation] = mutable.Map()
    Translate.global_eta_expand = eta_expand
    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background =
      Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)
    val thys = theory_graph.topological_order
    val theory_names = thys.map(node_name => node_name.toString)

    /** Opens for writing a .dk.part file associated to a session or theory,
     *  which, when closed, is copied to the corresponding .dk file
     */
    def new_dk_part_writer(name: String) =
      new Part_Writer(Path.explode(outdir+Prelude.mod_name(name)+".dk"))

    /** Reads the proof of theorem <code><span style="color:#FFC0CB;">serial</span></code>
     *  if there is one and returns a command declaring it as a lemma or axiom 
     */
    def decl_proof(serial: Long, theory_name: String): Syntax.Command = {
      read_proof(ses_cont, Thm_Id(serial,theory_name), other_cache=Some(term_cache)) match {
        case Some(proof) =>
          Translate.stmt_decl(Prelude.ref_proof_ident(serial), proof.prop, Some(proof.proof))
        case None =>
          error("proof "+serial+" not found!")
      }
    }

    /** map theory_name -> set of proofs in increasing order */
    val map_theory_proofs = mutable.Map[String, mutable.SortedSet[Long]]()
    // add an entry for each theory
    for (theory_name <- theory_names) {
      map_theory_proofs += (theory_name -> mutable.SortedSet[Long]())
    }

    /** the name of the module for orphan proofs (not in the current session theories) */
    val mod_name_orphans = Prelude.mod_name(session)+"_orphans"

    /** commands for orphan proofs */
    val orphan_commands = mutable.Queue[Syntax.Command]()

    // record proof idents and update map_theory_proofs or orphan_commands
    Prelude.set_theory_session(mod_name_orphans,session)
    Prelude.set_current_module(mod_name_orphans)
    for (entry_name <- ses_cont.entry_names()) {
      if (entry_name.name.startsWith(Export.PROOFS_PREFIX)) {
        val serial = entry_name.name.substring(7).toLong
        val theory_name = entry_name.theory
        if (verbose) progress.echo("  proof " + serial)
        if (map_theory_proofs.keySet.contains(theory_name)) {
          Prelude.add_proof_ident(serial,theory_name)
          map_theory_proofs(theory_name) += serial
        } else {
          Prelude.add_proof_ident(serial,mod_name_orphans)
          orphan_commands += (decl_proof(serial,theory_name))
        }
      }
    }

    if (!translate) { /* if translate is false, just update maps to keep in mind
                         the translated names of the session, but do not
                         write anything anywhere
                      */
      progress.echo("Start reading session "+session)
      for (thy <- thys) {
        val theory_name = thy.toString
        progress.echo("Start reading theory "+theory_name)
        val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
        val theory = read_theory(provider)
        for (a <- theory.types) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Prelude.add_type_ident(a.name,theory_name)
        }
        for (a <- theory.classes) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Prelude.add_class_ident(a.name,theory_name)
        }
        for (a <- theory.consts) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Prelude.add_const_ident(a.name,theory_name)
        }
        for (a <- theory.axioms) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Prelude.add_axiom_ident(a.name,theory_name)
        }
        for (a <- theory.thms) {
          if (verbose) progress.echo("  "+a.toString+" "+a.serial)
          Prelude.add_thm_ident(a.name,theory_name)
        }
        progress.echo("End reading theory "+theory_name)
      }
      progress.echo("End reading session "+session)
    }

    else {
      progress.echo("Start translating session "+session)
      /** name of the module for this session */
      val mod_name_session = "session_"+Prelude.mod_name(session)

      // set up generation of shell script to check dedukti files
      val filename = "dkcheck_"+mod_name_session+".sh"
      progress.echo("Start writing "+filename)
      val file = new File(outdir+filename)
      val sh = new BufferedWriter(new FileWriter(file))
      sh.write("#!/bin/sh\n")
      parent match {
        case Some(anc) =>
          sh.write("bash dkcheck_session_"+Prelude.mod_name(anc)+".sh\n")
          // write orphan proofs
          using (new_dk_part_writer(mod_name_orphans)) { part_writer =>
            progress.echo("Start writing "+mod_name_orphans+".dk")
            val orphan_writer = new DK_Writer(part_writer)
            orphan_writer.require("session_"+anc)
            orphan_writer.commands(orphan_commands,notations)
            progress.echo("End writing "+mod_name_orphans+".dk")
          }
        case _ =>
          sh.write("bash dkcheck_STTfa.sh\n")
      }
      sh.write("dk check -e --eta")
      parent match {
        case Some(anc) => sh.write(" "+mod_name_orphans+".dk")
        case _ =>
      }

      /* Open a dk file S for the session, then translate each theory of the
       * session in a dk file T, and simply import module T in S
       */
      using(new_dk_part_writer(mod_name_session)) { part_writer1 =>
        progress.echo("Start writing "+mod_name_session+".dk")
        val session_writer = new DK_Writer(part_writer1)

        for (thy <- thys) {
          val theory_name = thy.toString
          progress.echo("Start reading theory "+theory_name)
          val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
          val theory = read_theory(provider)
          session_writer.require(theory_name)
          val mod_name_theory = Prelude.mod_name(theory_name)
          
          sh.write(" "+mod_name_theory+".dk")
          using(new_dk_part_writer(mod_name_theory)) { part_writer2 =>
            val writer = new DK_Writer(part_writer2)
            progress.echo("Start writing "+mod_name_theory+".dk")
            writer.comment("Theory "+theory_name)
            // write module dependencies
            if (parent.isDefined) writer.require(mod_name_orphans)
            for (node_name <- theory_graph.imm_preds(thy)) {
              writer.require(node_name.toString)
            }
            Prelude.set_current_module(theory_name)
            // translate types
            writer.nl()
            writer.comment("Types")
            for (a <- theory.types) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.type_decl(theory_name, a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax)
              writer.command(cmd,notations)
            }
            /** map constant name -> definition */
            var map_cst_dfn:Map[String,Term] = Map()
            /** map definitional axiom name -> (type variables, the term it defines) */
            var map_axm_eqtyp:Map[String,(List[Typ],Term)] = Map()
            // check constant definitions
            for (a <- theory.consts) {
              a.the_content.abbrev match {
                case Some(d) =>
                  if (verbose) progress.echo(a.name+" has definition")
                  map_cst_dfn += (a.name -> d)
                case _ =>
              }
            }
            // check axioms
            for (a <- theory.axioms) {
              is_eq_axiom(a) match {
                case Some(n,d,eqtys,lhs) =>
                  if (verbose) progress.echo(n+" is defined by axiom "+a.name)
                  map_cst_dfn += (n -> d)
                  map_axm_eqtyp += (a.name -> (eqtys,lhs))
                case None =>
              }
            }
            // ordering on entities
            def le[A<:Content[A]](e1:Entity[A], e2:Entity[A]) = e1.serial <= e2.serial
            // Store declarations of defined classes and constants and definitional lemmas
            val defined_classes_decls = mutable.Queue[Syntax.Command]()
            val defined_constants_decls = mutable.Queue[Syntax.Command]()
            val definitional_lemmas_decls = Mutable.Queue[Syntax.Command]()
            // write declarations related to undefined classes
            if (verbose) progress.echo("Undefined classes")
            writer.nl()
            writer.comment("Undefined classes")
            for (a <- theory.classes.sortWith(le)) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val def_opt = map_cst_dfn.get(a.name+"_class")
              val cmd = Translate.class_decl(theory_name, a.name, def_opt)
              if (def_opt.isEmpty) writer.command(cmd,notations)
              else defined_classes_decls += cmd
            }
            // write declarations related to undefined constants
            writer.nl()
            writer.comment("Undefined constants")
            for (c <- theory.consts.sortWith(le)) {
              if (verbose) progress.echo("  "+c.toString+" "+c.serial)
              //skip constants corresponding to classes
              // TODO: from the previous comment,
              //       is everything not coming from a class named ..._Class ?
              if (c.name.endsWith("_Class")) 
                val def_opt = map_cst_dfn.get(c.name)
                val cmd = Translate.const_decl(theory_name, c.name, c.the_content.typargs, c.the_content.typ, def_opt, c.the_content.syntax)
                if (def_opt.isEmpty) writer.command(cmd,notations)
                else defined_constants_decls += cmd
            }
            // write declarations related to defined constants
            writer.nl()
            writer.comment("Defined constants")
            writer.commands(defined_constants_decls,notations)
            // write declarations related to defined classes
            if (verbose) progress.echo("Defined classes")
            writer.nl()
            writer.comment("Defined classes")
            writer.commands(defined_classes_decls,notations)
            // write declarations related to non-definitional axioms
            writer.nl()
            writer.comment("Axioms")
            for (a <- theory.axioms.sortWith(le)) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val def_opt = map_axm_eqtyp.get(a.name).map{
                case (eqtys,lhs) => Appt(PAxm("Pure.reflexive",eqtys),lhs)
              }
              val cmd = Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, def_opt)
              if (def_opt.isEmpty) writer.command(cmd,notations)
              else definitional_lemmas_decls += cmd
            }
            // write declarations related to definitional axioms
            writer.nl()
            writer.comment("Definitional theorems")
            writer.commands(definitional_lemmas_decls,notations)
            
            /** function writing a declaration related to a theorem */
            def decl_thm(thm : Entity[Thm]): Unit = {
              if (verbose) progress.echo("  "+thm.toString+" "+thm.serial)
              val cmd = Translate.stmt_decl(Prelude.add_thm_ident(thm.name,theory_name), thm.the_content.prop, Some(thm.the_content.proof))
              writer.command(cmd, notations)
            }

            /** function writing all the proofs in prfs,
             *  also declaring all theorems in thms once 
             *  their [[max_serial]] has been reached
             *  
             * @param prfs proofs to handle
             * @param thms remaining theorems
             */
            @tailrec
            def write_proofs(prfs: List[Long], thms: List[Entity[Thm]]) : Unit =
              thms match {
                case thm :: thms =>
                  write_proofs_body(prfs,thm,thms,max_serial(thms))
                case _ => write_proofs_body(prfs,null,Nil,Long.MaxValue)
              }
              
            @tailrec
            def write_proofs_body(prfs: List[Long], thm: Entity[Thm], thms: List[Entity[Thm]], thm_prf: Long): Unit =
              prfs match {
                case prf::prfs2 =>
                  if (prf > thm_prf) {
                    // all proofs <= thm_prf have been handled already
                    decl_thm(thm)
                    write_proofs(prfs2,thms)
                  } else {
                    if (verbose) progress.echo("  proof "+prf)
                    val cmd = decl_proof(prf,theory_name)
                    writer.command(cmd,notations)
                    write_proofs_body(prfs2,thm,thms,thm_prf)
                  }
                case _ =>
              }
            // write declarations related to theorems
            writer.nl()
            writer.comment("Theorems")
            // all proofs in increasing order
            val prfs = map_theory_proofs(theory_name).toList
            write_proofs(theory.thms)
            progress.echo("End writing "+mod_name_theory+".dk")
          }
          progress.echo("End reading theory "+theory_name)
        }
        sh.write(" "+mod_name_session+".dk\n")
        sh.close()
        progress.echo("End writing "+mod_name_session+".dk")
      }
      progress.echo("End translating session "+session)
    }
  }
}
