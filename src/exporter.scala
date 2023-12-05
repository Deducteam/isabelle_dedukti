/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle._

import scala.collection.mutable
import scala.util.control.Breaks._

object Exporter {

  def max_serial(thm: Export_Theory.Entity[Export_Theory.Thm]): Long = {
    def sub(p:Term.Proof) : Long = p match {
      case Term.PThm(serial,_,_,_) => serial
      case Term.Appt(p,_) => sub(p)
      case Term.AppP(p,q) => Math.max(sub(p), sub(q))
      case Term.Abst(_,_,b) => sub(b)
      case Term.AbsP(_,_,b) => sub(b)
      case _ => 0
    }
    sub(thm.the_content.proof)
  }

  def read_entry_names_of_theory(db: SQL.Database, session_name: String, theory_name: String): List[Export.Entry_Name] = {
    val select =
      Export.private_data.Base.table.select(List(Export.private_data.Base.theory_name, Export.private_data.Base.name), sql = Export.private_data.where_equal(session_name,theory_name))
    db.using_statement(select)(stmt =>
      stmt.execute_query().iterator(res =>
        Export.Entry_Name(session = session_name,
          theory = res.string(Export.private_data.Base.theory_name),
          name = res.string(Export.private_data.Base.name))).toList)
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
    verbose: Boolean = false
  ): Unit = {
    val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()
    Translate.global_eta_expand = eta_expand
    def filename_lp(module: String) = Path.explode (session + "/lambdapi/" + Prelude.mod_name(module) + ".lp")
    def filename_dk(module: String) = Path.explode (session + "/dkcheck/" + Prelude.mod_name(module) + ".dk")
    def write_lp(
      module: String,
      commands: mutable.Queue[Syntax.Command],
      deps: List[String]
    ): Unit = {
      using(new Part_Writer(filename_lp(module))) { part_writer =>
        val writer = new LP_Writer(use_notations, part_writer)
        writer.comment("Lambdapi translation of " + session + "." + module)
        progress.echo("Write theory \"" + module + "\" in Lambdapi...")
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
    def write_dk(
      module: String,
      commands: mutable.Queue[Syntax.Command],
      deps: List[String]
    ): Unit = {
      using(new Part_Writer(filename_dk(module))) { part_writer =>
        val writer = new DK_Writer(part_writer)
        writer.comment("Dedukti translation of " + session + "." + module)
        progress.echo("Write theory \"" + module + "\" in Dedukti...")
        for (dep <- deps) { writer.require(dep) }
        for (command <- commands) {
          command match {
            case Syntax.Definition(_,_,_,_,_) =>
            case command => writer.command(command, notations)
          }
        }
      }
    }
    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background = Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)

    // turns proof index into a command
    def prf_command(prf: Long, theory_name: String): Syntax.Command = {
      Export_Theory.read_proof(ses_cont, Export_Theory.Thm_Id(prf,theory_name),other_cache=Some(term_cache)) match {
        case Some(proof) =>
          Translate.stmt_decl(Prelude.ref_proof_ident(prf), proof.prop, Some(proof.proof))
        case None =>
          error("proof "+prf+" not found!")
      }
    }

    progress.echo((if (translate) "Translating" else "Reading") + " session " + session + " ...")

    val thys = theory_graph.topological_order
    val theory_names = thys.map(node_name => node_name.toString)

    if (translate) {
      write_dk(session, mutable.Queue(), theory_names)
      write_lp(session, mutable.Queue(), theory_names)
    }
    // remember to which module each proof should belong
    val prfs_of_module = mutable.Map[String/* module name */, mutable.SortedSet[Long]]()
    for (theory_name <- theory_names) {
      prfs_of_module+=(theory_name -> mutable.SortedSet[Long]())
    }

    // parent_session_module is the special one for the proofs belonging to the theories of the parent session, but not generated in the parent session
    val parent_session_module = session + "_Parent"
    Prelude.set_theory_session(parent_session_module,session)
    Prelude.set_current_module(parent_session_module)
    {
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
            session_commands+=(prf_command(prf,theory_name))
          }
        }
      }

      // writing orphan proofs
      if (translate) parent match {
        case Some(anc) =>
          write_dk(parent_session_module,session_commands,List(anc))
          write_lp(parent_session_module,session_commands,List(anc))
        case _ =>
      }

    }// release session_commands etc.

    // writing theories
    for (thy <- thys) {
      val theory_name = thy.toString
      Prelude.set_current_module(theory_name)
      val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
      val theory = Export_Theory.read_theory(provider)

      if (!translate) {
        progress.echo("Read theory " + theory_name + " ...")
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
      } else {
        progress.echo("Translate proofs for " + theory_name + " ...")
        val current_commands = mutable.Queue[Syntax.Command]()
        for (a <- theory.classes) {
          if (verbose) progress.echo("  " + a.toString + a.serial)
          current_commands.append(Translate.class_decl(theory_name, a.name))
        }
        for (a <- theory.types) {
          if (verbose) progress.echo("  " + a.toString + a.serial)
          current_commands.append(Translate.type_decl(theory_name, a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))
        }
        for (a <- theory.consts) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          current_commands.append(Translate.const_decl(theory_name, a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))
        }
        for (a <- theory.axioms) {
          if (verbose) progress.echo("  " + a.toString + " " + a.serial)
          current_commands.append(Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, None))
        }

        def translate_thm(thm : Export_Theory.Entity[Export_Theory.Thm]): Unit = {
          if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
          current_commands.append(Translate.stmt_decl(Prelude.add_thm_ident(thm.name,theory_name), thm.the_content.prop, Some(thm.the_content.proof)))
        }

        def prf_loop(
          prfs : List[Long],
          thm : Export_Theory.Entity[Export_Theory.Thm],
          thms : List[Export_Theory.Entity[Export_Theory.Thm]],
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
              if (verbose) progress.echo("  proof " + prf)
              current_commands.append(prf_command(prf,theory_name))
              prf_loop(prfs2,thm,thms,thm_prf)
            }
          case _ =>
        }

        if (verbose) progress.echo("reading proofs")
        val prfs = prfs_of_module(theory_name).toList
        theory.thms match {
          case thm :: thms => prf_loop(prfs,thm,thms,max_serial(thm))
          case _ => prf_loop(prfs,null,null,Long.MaxValue)
        }
        def deps = parent_session_module :: theory_graph.imm_succs(thy).toList.map(node_name => node_name.toString)
        write_dk(theory_name,current_commands,deps)
        write_lp(theory_name,current_commands,deps)
      }
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
