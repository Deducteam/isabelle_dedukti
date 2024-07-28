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

              // head and arguments in reverse order of a term
            def head_revargs(t:Term,args:List[Term]): (Term,List[Term]) = {
              t match {
                case App(u,v) => head_revargs(u,v::args)
                case _ => (t,args.reverse)
              }
            }
            // tell if a term is a free variable
            def is_free(t:Term): Boolean = {
              t match {
                case Free(_,_) => true
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
                case _ => error("oops "+arg.toString)
              }
            }
            // constant name and definition from an equality
            def is_eq(t:Term):Option[(String,Term)] = {
              t match {
                case App(u,r) =>
                  u match {
                    case App(e,l) =>
                      e match {
                        case Cst(n,_) =>
                          if (n != "Pure.eq") None
                          else {
                            val (h,revargs) = head_revargs(l,List()) 
                            h match {
                              case Cst(n,_) =>
                                if (n.contains("_class.")) None
                                else {
                                  if (revargs.forall(is_free)) {
                                    val r2 = debruijn(revargs,r)
                                    val d = revargs.foldLeft(r2)(abs)
                                    /*println("t: "+t.toString)
                                    println("revargs: "+revargs.toString)
                                    println("r: "+r.toString)
                                    println("debruijn: "+r2.toString)
                                    println("d: "+d.toString)*/
                                    Some(n,d)
                                  } else None
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
            }
            // constant name and definition from an axiom
            def is_eq_axiom(a:Entity[Axiom]):Option[(String,Term)] = {
              if (a.name.endsWith("_def") || a.name.endsWith("_def_raw")) {
                val t = a.the_content.prop.term
                is_eq(t) /*match {
                  case None =>
                    println("could not extract definition from "+a.name)
                    None
                  case v => v
                }*/
              } else None
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

    val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()
    Translate.global_eta_expand = eta_expand
    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background = Document_Build.session_background(options, session, dirs = dirs)
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
    val session_commands = mutable.Queue[Syntax.Command]()

    // record proof idents and update map_theory_proofs or session_commands    
    Prelude.set_theory_session(mod_name_orphans,session)
    Prelude.set_current_module(mod_name_orphans)
    for (entry_name <- ses_cont.entry_names()) {
      if (entry_name.name.startsWith("proofs/")) {
        val serial = entry_name.name.substring(7).toLong
        val theory_name = entry_name.theory
        if (verbose) progress.echo("  proof " + serial)
        if (map_theory_proofs.keySet.contains(theory_name)) {
          Prelude.add_proof_ident(serial,theory_name)
          map_theory_proofs(theory_name) += (serial)
        } else {
          Prelude.add_proof_ident(serial,mod_name_orphans)
          session_commands += (decl_proof(serial,theory_name))
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
            for (cmd <- session_commands) {
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
            // write declarations related to classes
            writer.nl()
            writer.comment("Classes")
            for (a <- theory.classes) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.class_decl(theory_name, a.name)
              writer.command(cmd,notations)
            }
            // map constant name -> definition
            var dfn_map:Map[String,Term] = Map()
            for (a <- theory.axioms) {
              is_eq_axiom(a) match {
                case Some(n,d) =>
                  //progress.echo("axiom: "+a.the_content.prop.toString)
                  //progress.echo(n+" is defined by "++d.toString)
                  /*val ds = dfn_map.get(n) match {
                    case None => List()
                    case Some(ds) => d::ds
                  }*/
                  dfn_map += (n -> d)
                case None =>
              }
            }
            // get the definition of a constant
            def dfn(c:Entity[Const]): Option[Term] = {
              c.the_content.abbrev match {
                case None => dfn_map.get(c.name)
                case v => v
              }
            }
            // type of dependency graphs between constants
            type GraphConst = Graph[String,Unit]
            // add dependencies from a constant definition
            def add_deps_dfn(c:String, t:Term, g:GraphConst): GraphConst = {
              def aux(t:Term, g:GraphConst): GraphConst = {
                t match {
                  case Cst(n,_) => g.default_node(n,()).add_edge(c,n)
                  case App(u,v) => aux(v,aux(u,g))
                  case Abs(_,_,u) => aux(u,g)
                  case _ => g
                }
              }
              aux(t,g)
            }
            // add dependencies of a constant
            def add_deps_const(c:Entity[Const], g:GraphConst): GraphConst = {
              val g1 = g.default_node(c.name,())
              dfn(c) match {
                case Some(d) => add_deps_dfn(c.name,d,g1)
                case _ => g1
              }
            }
            // dependency graph between constants
            val g0 : GraphConst = Graph.empty(Ordering.String)
            val g : GraphConst = 
              theory.consts.foldRight(g0)(add_deps_const).transitive_closure
            // le(c1,c2)=true iff c1 can be declared before c2
            val const_names = g.topological_order.reverse
            def le(c1:Entity[Const], c2:Entity[Const]):Boolean = {
              if (const_names.indexOf(c1.name)
                <= const_names.indexOf(c2.name)) true
              else false
            }
            val constants = theory.consts.sortWith(le)
            // write declarations related to constants
            writer.nl()
            writer.comment("Constants")
            for (a <- constants) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.const_decl(theory_name, a.name, a.the_content.typargs, a.the_content.typ, dfn_map.get(a.name), a.the_content.syntax)
              writer.command(cmd,notations)
            }
            // write declarations related to axioms
            writer.nl()
            writer.comment("Axioms")
            for (a <- theory.axioms) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, None)
              writer.command(cmd,notations)
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
