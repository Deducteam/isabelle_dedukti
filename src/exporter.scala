/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle._
import isabelle.Term.{Const => Cst, Proof => Prf, _}
import isabelle.Export_Theory._

import java.io._
import scala.collection.mutable
import scala.util.control.Breaks._

object Exporter {

  def max_serial(thm: Entity[Thm]): Long = {
    def sub(p:Prf) : Long = p match {
      case PThm(serial,_,_,_) => serial
      case Appt(p,_) => sub(p)
      case AppP(p,q) => Math.max(sub(p), sub(q))
      case Abst(_,_,b) => sub(b)
      case AbsP(_,_,b) => sub(b)
      case _ => 0
    }
    sub(thm.the_content.proof)
  }

  def module_of_session(session: String) = "session_"+session

  def filename_lp(session: String, module: String) = Path.explode (session + "/lambdapi/" + Prelude.mod_name(module) + ".lp")

  def write_lp(
    session: String,
    module: String,
    commands: mutable.Queue[Syntax.Command],
    deps: List[String],
    eta_expand: Boolean,
    use_notations: Boolean,
    notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation]
  ): Unit = {
    using(new Part_Writer(filename_lp(session,module))) { part_writer =>
      val writer = new LP_Writer(use_notations, part_writer)
      writer.comment("Lambdapi translation of " + session + "." + module)
      if (!eta_expand) writer.eta_equality()
      for (dep <- deps) { writer.require(dep) }
      for (command <- commands) {
        command match {
          case Syntax.Definition(_,_,_,_,_) =>
          case command => writer.command(command, notations)
        }
      }
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
    def new_dk_part_writer(module: String) =
      new Part_Writer(Path.explode (outdir + Prelude.mod_name(module) + ".dk"))

    val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()
    Translate.global_eta_expand = eta_expand
    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background = Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)

    // turns proof index into a command
    def prf_command(prf: Long, theory_name: String): List[Syntax.Command] = {
      read_proof(ses_cont, Thm_Id(prf,theory_name),other_cache=Some(term_cache)) match {
        case Some(proof) =>
          Translate.stmt_decl(Prelude.ref_proof_ident(prf), proof.prop, Some(proof.proof))
        case None =>
          error("proof "+prf+" not found!")
      }
    }

    val thys = theory_graph.topological_order
    val theory_names = thys.map(node_name => node_name.toString)

    // remember to which module each proof should belong
    val prfs_of_module = mutable.Map[String/* module name */, mutable.SortedSet[Long]]()
    for (theory_name <- theory_names) {
      prfs_of_module+=(theory_name -> mutable.SortedSet[Long]())
    }

    // parent_session_module is the special one for the proofs belonging to the theories of the parent session, but not generated in the parent session
    val parent_session_module = "parent_" + session
    Prelude.set_theory_session(parent_session_module,session)
    Prelude.set_current_module(parent_session_module)

    // collects commands that doesn't belong to any theory of the current session
    val session_commands = mutable.Queue[Syntax.Command]()

    for (entry_name <- ses_cont.entry_names()) {
      if (entry_name.name.startsWith("proofs/")) {
        val prf = entry_name.name.substring(7).toLong
        val theory_name = entry_name.theory
        // if (verbose) progress.echo("  proof " + prf + " from " + entry_name.theory)
        if (prfs_of_module.keySet.contains(theory_name)) {
          Prelude.add_proof_ident(prf,theory_name)
          prfs_of_module(theory_name)+=(prf)
        } else {// the proof is attributed to a theory of a parent session
          Prelude.add_proof_ident(prf,parent_session_module)
          if (verbose) progress.echo("  proof " + prf)
          session_commands ++= (prf_command(prf,theory_name))
        }
      }
    }

    if (!translate) {
      progress.echo("Start reading session "+session+" ...")
      for (thy <- thys) {
        val theory_name = thy.toString
        val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
        val theory = read_theory(provider)

        progress.echo("Read theory "+theory_name+" ...")
        for (a <- theory.classes) {
          if (verbose) progress.echo("  " + a.toString + a.serial)
          Prelude.add_class_ident(a.name,theory_name)
        }
        for (a <- theory.types) {
          if (verbose) progress.echo("  " + a.toString + a.serial)
          Prelude.add_type_ident(a.name,theory_name)
        }
        for (a <- theory.consts) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          Prelude.add_const_ident(a.name,theory_name)
        }
        for (a <- theory.axioms) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          Prelude.add_axiom_ident(a.name,theory_name)
        }
        for (a <- theory.thms) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          Prelude.add_thm_ident(a.name,theory_name)
        }
      }
      progress.echo("End reading session "+session)
    } else {
      progress.echo("Start translating session "+session)
      val filename3 = "dkcheck_"+Prelude.mod_name(session)+".sh"
      progress.echo("Write "+filename3+" ...")
      val file3 = new File(outdir+filename3)
      val bw3 = new BufferedWriter(new FileWriter(file3))
      bw3.write("#!/bin/sh\n")
      parent match {
        case Some(anc) =>
          bw3.write("bash dkcheck_"+anc+".sh\n")
          // write orphan proofs
          using (new_dk_part_writer(parent_session_module)) { part_writer =>
            val writer = new DK_Writer(part_writer)
            writer.require(module_of_session(anc))
            for (cmd <- session_commands) {
              writer.command(cmd,notations)
            }
          }
        case _ =>
          bw3.write("bash dkcheck_STTfa.sh\n")
      }
      bw3.write("dk check -e --eta")
      parent match {
        case Some(anc) => bw3.write(" "+parent_session_module+".dk")
        case _ =>
      }
      // the session module, importing all the theories of the session
      val session_module = module_of_session(session)
      using(new_dk_part_writer(session_module)) { part_writer =>
        val session_writer = new DK_Writer(part_writer)

        // reading theories
        for (thy <- thys) {
          val theory_name = thy.toString
          val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
          val theory = read_theory(provider)
          session_writer.require(theory_name)

          using(new_dk_part_writer(theory_name)) { part_writer =>
            val writer = new DK_Writer(part_writer)
            progress.echo("Write "+Prelude.mod_name(theory_name)+".dk ...")
            writer.comment("Session "+session+"."+theory_name)
            // write module dependencies
            if (parent != None) writer.require(parent_session_module)
            for (node_name <- theory_graph.imm_preds(thy)) {
              writer.require(node_name.toString)
            }
            Prelude.set_current_module(theory_name)
            writer.nl()
            writer.comment("Classes")
            for (a <- theory.classes) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.class_decl(theory_name, a.name)
              writer.command(cmd,notations)
            }
            writer.nl()
            writer.comment("Types")
            for (a <- theory.types) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.type_decl(theory_name, a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax)
              writer.command(cmd,notations)
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
                                    /*progress.echo("t: "+t.toString)
                                    progress.echo("revargs: "+revargs.toString)
                                    progress.echo("r: "+r.toString)
                                    progress.echo("debruijn: "+r2.toString)
                                    progress.echo("d: "+d.toString)*/
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
                    progress.echo("could not extract definition from "+a.name)
                    None
                  case v => v
                }*/
              } else None
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
            // definition of a constant
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
            // output constants
            writer.nl()
            writer.comment("Constants")
            for (a <- constants) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              val cmd = Translate.const_decl(theory_name, a.name, a.the_content.typargs, a.the_content.typ, dfn_map.get(a.name), a.the_content.syntax)
              writer.command(cmd,notations)
            }
            // output axioms
            writer.nl()
            writer.comment("Axioms")
            for (a <- theory.axioms) {
              if (verbose) progress.echo("  "+a.toString+" "+a.serial)
              Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, None) match {
                case List(c) => writer.command(c,notations)
                case List(_,c) => writer.command(c,notations)
                case _ => error("oops")
              }
            }

            def translate_thm(thm : Entity[Thm]): Unit = {
              if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
              val cmds = Translate.stmt_decl(Prelude.add_thm_ident(thm.name,theory_name), thm.the_content.prop, Some(thm.the_content.proof))
              cmds.foreach(cmd => writer.command(cmd, notations))
            }

            def prf_loop(
              prfs : List[Long],
              thm : Entity[Thm],
              thms : List[Entity[Thm]],
              thm_prf : Long
            ) : Unit = prfs match {
              case prf::prfs2 =>
                if (prf > thm_prf) {
                  translate_thm(thm)
                  // progress.echo("  Ready for thm " + prf + " > " + thm_prf)
                  thms match {
                    case thm2 :: thms2 =>
                      prf_loop(prfs,thm2,thms2,max_serial(thm2))
                    case Nil =>
                      prf_loop(prfs,null,null,Long.MaxValue)
                  }
                } else {
                  if (verbose) progress.echo("  proof "+prf)
                  val cmds = prf_command(prf,theory_name)
                  cmds.foreach(cmd => writer.command(cmd,notations))
                  prf_loop(prfs2,thm,thms,thm_prf)
                }
              case _ =>
            }

            writer.nl()
            writer.comment("Proofs")
            val prfs = prfs_of_module(theory_name).toList
            theory.thms match {
              case thm :: thms => prf_loop(prfs,thm,thms,max_serial(thm))
              case _ => prf_loop(prfs,null,null,Long.MaxValue)
            }
          }
          bw3.write(" "+Prelude.mod_name(theory.toString)+".dk")
        }
        bw3.write(" "+session_module+".dk\n")
        bw3.close()
      }
      progress.echo("End translating session "+session)
    }
  }
/*
  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_theory"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "export theory content to Dedukti or Lambdapi", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION THEORY

  Options are:
    -d DIR       include session directory
    -e           remove need for eta flag
    -l           generate Lambdapi files instead of Dedukti files
    -n           use lambdapi notations
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Export the specified THEORY of SESSION to a Dedukti or Lambdapi file with the same name except that every dot is replaced by an underscore.""",

        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "e" -> (_ => eta_expand = true),
        "n" -> (_ => use_notations = true),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true))

        val more_args = getopts(args)

        val (session,theory) =
          more_args match {
            case List(session,theory) => (session,theory)
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try exporter(options, session, List(theory), true, Term.Cache.make(), progress, dirs, use_notations, eta_expand, verbose)
          catch {case x: Exception =>
            progress.echo(x.getStackTrace.mkString("\n"))
            println(x)}
          finally {
            val end_date = Date.now()
            if (verbose) progress.echo("\nFinished at " + Build_Log.print_date(end_date))
            progress.echo((end_date.time - start_date.time).message_hms + " elapsed time")
          }
        }
      }
    )
*/
}
