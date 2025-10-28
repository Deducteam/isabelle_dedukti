/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle._
import isabelle.Term.{Const => Cst, Proof => Prf, _}
import isabelle.Export_Theory._

import java.io._
import scala.collection.mutable
import scala.util.control.Breaks._

object Exporter {

  // compute the biggest theorem serial occurring in a theorem
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

  // head and arguments of a term
  def head_args(t:Term,args:List[Term]): (Term,List[Term]) = {
    t match {
      case App(u,v) => head_args(u,v::args)
      case _ => (t,args)
    }
  }

  // tell if a term is a free variable or Pure_Thy.TYPE
  def is_Free_or_TYPE(t:Term): Boolean = {
    t match {
      case Free(_,_) => true
      case Term.Const(Pure_Thy.TYPE, List(TFree("'a",Nil))) => true
      case _ => false
    }
  }

  // tell if a type is a free variable
  def is_TFree(t:Typ): Boolean = {
    t match {
      case TFree(_,_) => true
      case _ => false
    }
  }

  // replace free variables by De Bruijn indices
  def debruijn(revargs:List[Term], t:Term): Term = {
    t match {
      case Free(n,ty) => Bound(revargs.indexOf(t))
      case App(u,v) => App(debruijn(revargs,u),debruijn(revargs,v))
      case Abs(n,ty,b) => Abs(n,ty,debruijn(Free(n,ty)::revargs,b))
      case _ => t
    }
  }

  // build an abstraction assuming that arg is a free variable
  def abs(b:Term, arg:Term): Term = {
    arg match {
      case Free(n,ty) => Abs(n,ty,b)
      case _ => error("exporter.abs: not a free variable "+arg.toString)
    }
  }

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

    /* from an equality [Pure.eq[eqtys] lhs rhs] where [lhs = c[tys] x1
     * .. xn] with tys and xj variables, returns (c,dfn,eqtys,lhs)
     * where [dfn=\x1..\xn,rhs] */
    def is_eq_axiom(a:Entity[Axiom]):Option[(String,Term,List[Typ],Term)] = {
      if (a.name.endsWith("_def") || a.name.endsWith("_def_raw")) {
        a.the_content.prop.term match {
          case App(u,rhs) =>
            u match {
              case App(e,lhs) =>
                e match {
                  case Cst(id,eqtys) =>
                    if (id != "Pure.eq") {
                      if (verbose) progress.echo("axiom "+a.name+": cannot extract definition because it is headed by "+id+" instead of Pure.eq")
                      None
                    } else {
                      val (h,args) = head_args(lhs,List())
                      h match {
                        case Cst(n,tys) =>
                          if (tys.forall(is_TFree) && args.forall(is_Free_or_TYPE)) {
                            if (verbose) progress.echo("  head: "+h.toString+"\n  args: "+args.toString+"\n  rhs: "+rhs.toString)
                            args match {
                              case List(Term.Const(Pure_Thy.TYPE,List(TFree(x,Nil)))) =>
                                lhs match {
                                  case OFCLASS(_,_) => Some(n,rhs,eqtys,lhs)
                                  case _ => None
                                }
                              case _ =>
                                val revargs = args.reverse
                                val rhs2 = debruijn(revargs,rhs)
                                val dfn = revargs.foldLeft(rhs2)(abs)
                                Some(n,dfn,eqtys,lhs)
                            }
                          } else {
                            if (verbose) progress.echo("axiom "+a.name+": cannot extract definition because it is not applied to free variables\n  axiom: "+a.the_content.prop.term.toString+"\n  type arguments: "+tys.toString+"\n  term arguments: "+args.toString)
                            None
                          }
                        case _ => None
                      }
                    }
                  case _ => None
                }
              case _ => None
            }
          case _ => None
        }
      } else None
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

    // file associated to a session or theory
    def new_dk_part_writer(name: String) =
      new Part_Writer(Path.explode(outdir+Prelude.mod_name(name)+".dk"))

    // command for a proof
    def decl_proof(serial: Long, theory_name: String): Syntax.Command = {
      read_proof(ses_cont, Thm_Id(serial,theory_name), other_cache=Some(term_cache)) match {
        case Some(proof) =>
          Translate.stmt_decl(Prelude.ref_proof_ident(serial), proof.prop, Some(proof.proof))
        case None =>
          error("proof "+serial+" not found!")
      }
    }

    // map theory_name -> proofs in increasing order
    val map_theory_proofs = mutable.Map[String, mutable.SortedSet[Long]]()
    // add an entry for each theory
    for (theory_name <- theory_names) {
      map_theory_proofs += (theory_name -> mutable.SortedSet[Long]())
    }

    // module for orphan proofs (not in the current session theories)
    val mod_name_orphans = Prelude.mod_name(session)+"_orphans"

    // commands for orphan proofs
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
          map_theory_proofs(theory_name) += (serial)
        } else {
          Prelude.add_proof_ident(serial,mod_name_orphans)
          orphan_commands += (decl_proof(serial,theory_name))
        }
      }
    }

    if (!translate) {
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
            for (cmd <- orphan_commands) {
              orphan_writer.command(cmd,notations)
            }
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

      // generate the dedukti file importing all the theories of the session
      using(new_dk_part_writer(mod_name_session)) { part_writer =>
        progress.echo("Start writing "+mod_name_session+".dk")
        val session_writer = new DK_Writer(part_writer)

        for (thy <- thys) {
          val theory_name = thy.toString
          progress.echo("Start reading theory "+theory_name)
          val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
          val theory = read_theory(provider)
          session_writer.require(theory_name)
          val mod_name_theory = Prelude.mod_name(theory_name)

          // generate the dedukti file of the theory
          sh.write(" "+mod_name_theory+".dk")
          using(new_dk_part_writer(mod_name_theory)) { part_writer =>
            val writer = new DK_Writer(part_writer)
            progress.echo("Start writing "+mod_name_theory+".dk")
            writer.comment("Theory "+theory_name)
            // write module dependencies
            if (parent != None) writer.require(mod_name_orphans)
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
            // map constant name -> definition * definitional axiom
            var map_cst_dfn:Map[String,Term] = Map()
            // names of definitional axioms
            var map_axm_eqtyp:Map[String,(List[Typ],Term)] = Map()
            // check constant abbreviations
            for (a <- theory.consts) {
              a.the_content.abbrev match {
                case Some(d) =>
                  if (verbose) progress.echo(a.name+" has abbreviation")
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
            // write declarations related to undefined classes
            if (verbose) progress.echo("Undefined classes")
            writer.nl()
            writer.comment("Undefined classes")
            for (a <- theory.classes.sortWith(le)) {
              map_cst_dfn.get(a.name+"_class") match {
                case None =>
                  if (verbose) progress.echo("  "+a.toString+" "+a.serial)
                  val cmd = Translate.class_decl(theory_name, a.name, None)
                  writer.command(cmd,notations)
                case Some(_) =>
              }
            }
            // write declarations related to undefined constants
            writer.nl()
            writer.comment("Undefined constants")
            for (c <- theory.consts.sortWith(le)) {
              // skip constants corresponding to classes
              if (c.name.endsWith("_Class")) {
                map_cst_dfn.get(c.name) match {
                  case None =>
                    if (verbose) progress.echo("  "+c.toString+" "+c.serial)
                    val cmd = Translate.const_decl(theory_name, c.name, c.the_content.typargs, c.the_content.typ, None, c.the_content.syntax)
                    writer.command(cmd,notations)
                  case Some(_) =>
                }
              }
            }
            // write declarations related to defined constants
            writer.nl()
            writer.comment("Defined constants")
            for (c <- theory.consts.sortWith(le)) {
              // skip constants corresponding to classes
              if (c.name.endsWith("_Class")) {
                map_cst_dfn.get(c.name) match {
                  case None =>
                  case Some(dfn) =>
                    if (verbose) progress.echo("  "+c.toString+" "+c.serial)
                    val cmd = Translate.const_decl(theory_name, c.name, c.the_content.typargs, c.the_content.typ, Some(dfn), c.the_content.syntax)
                    writer.command(cmd,notations)
                }
              }
            }
            // write declarations related to defined classes
            if (verbose) progress.echo("Defined classes")
            writer.nl()
            writer.comment("Defined classes")
            for (a <- theory.classes.sortWith(le)) {
              map_cst_dfn.get(a.name+"_class") match {
                case Some(d) =>
                  if (verbose) progress.echo("  "+a.toString+" "+a.serial+" := "+d.toString)
                  val cmd = Translate.class_decl(theory_name, a.name, Some(d))
                  writer.command(cmd,notations)
                case None =>
              }
            }
            // write declarations related to non-definitional axioms
            writer.nl()
            writer.comment("Axioms")
            for (a <- theory.axioms.sortWith(le)) {
              if (!map_axm_eqtyp.contains(a.name)) {
                if (verbose) progress.echo("  "+a.toString+" "+a.serial)
                val cmd = Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, None)
                writer.command(cmd,notations)
              }
            }
            // write declarations related to definitional axioms
            writer.nl()
            writer.comment("Definitional theorems")
            for (a <- theory.axioms.sortWith(le)) {
              map_axm_eqtyp.get(a.name) match {
                case None =>
                case Some(eqtys,lhs) =>
                  if (verbose) progress.echo("  "+a.toString+" "+a.serial)
                  val p = a.the_content.prop
                  val prf = Appt(PAxm("Pure.reflexive",eqtys),lhs)
                  //println("proof of "+a.name+": "+prf.toString)
                  val cmd = Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, Some(prf))
                  writer.command(cmd,notations)
              }
            }
            // function writing a declaration related to a theorem
            def decl_thm(thm : Entity[Thm]): Unit = {
              if (verbose) progress.echo("  "+thm.toString+" "+thm.serial)
              val cmd = Translate.stmt_decl(Prelude.add_thm_ident(thm.name,theory_name), thm.the_content.prop, Some(thm.the_content.proof))
              writer.command(cmd, notations)
            }
            // function writing declarations related to theorems
            def write_proofs(
              prfs : List[Long], // proofs to handle
              thm : Entity[Thm], // first theorem to handle
              thms : List[Entity[Thm]], // remaining theorems
              thm_prf : Long // maximal proof index in thm
            ) : Unit = prfs match {
              case prf::prfs2 =>
                if (prf > thm_prf) {
                  // all proofs <= thm_prf have been handled already
                  decl_thm(thm)
                  thms match {
                    case thm2 :: thms2 =>
                      write_proofs(prfs,thm2,thms2,max_serial(thm2))
                    case Nil =>
                      write_proofs(prfs,null,Nil,Long.MaxValue)
                  }
                } else {
                  if (verbose) progress.echo("  proof "+prf)
                  val cmd = decl_proof(prf,theory_name)
                  writer.command(cmd,notations)
                  write_proofs(prfs2,thm,thms,thm_prf)
                }
              case _ =>
            }
            // write declarations related to theorems
            writer.nl()
            writer.comment("Theorems")
            // all proofs in increasing order
            val prfs = map_theory_proofs(theory_name).toList
            theory.thms match {
              case thm :: thms => write_proofs(prfs,thm,thms,max_serial(thm))
              case _ => write_proofs(prfs,null,Nil,Long.MaxValue)
            }
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
