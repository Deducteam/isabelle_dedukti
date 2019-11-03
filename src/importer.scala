/** Isabelle/Dedukti importer (lp syntax) **/


package isabelle.dedukti

import isabelle._
import scala.collection.mutable.ListBuffer

object Importer
{
  /* importer */

  val default_output_file: Path = Path.explode("output.lp")

  def importer(
    options: Options,
    progress: Progress = No_Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_file: Path = default_output_file,
    selection: Sessions.Selection = Sessions.Selection.empty,
    verbose: Boolean = false)
  {
    val store = Sessions.store(options)
    val cache = Term.make_cache()

    val logic = Thy_Header.PURE

    val dump_options =
      if (options.bool("export_standard_proofs")) {
        options + "record_proofs=2" + "prune_proofs=false"
      }
      else options + "record_proofs=2" + "export_proofs" + "prune_proofs"

    val context =
      Dump.Context(dump_options,
        aspects = Dump.known_aspects, progress = progress,
        dirs = dirs, select_dirs = select_dirs, selection = selection)

    context.build_logic(logic)


    /* import theory content */

    var exported_proofs = Set.empty[Long]

    def import_theory(
      output: LP_Syntax.Output,
      theory: Export_Theory.Theory,
      provider: Export.Provider)
    {
      progress.echo("Importing theory " + theory.name)

      output.string("\n\n// theory " + theory.name + "\n\n")

      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.entity.toString)
        output.class_decl(a.entity.name)
      }

      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.entity.toString)

        a.abbrev match {
          case None => output.type_decl(a.entity.name, a.args.length)
          case Some(rhs) => output.type_abbrev(a.entity.name, a.args, rhs)
        }

        if (a.entity.name == Pure_Thy.FUN) output.prelude_fun
        if (a.entity.name == Pure_Thy.PROP) output.prelude_prop
      }

      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.entity.toString)

        a.abbrev match {
          case None => output.const_decl(a.entity.name, a.typargs, a.typ)
          case Some(rhs) => output.const_abbrev(a.entity.name, a.typargs, a.typ, rhs)
        }

        if (a.entity.name == Pure_Thy.ALL) output.prelude_all
        if (a.entity.name == Pure_Thy.IMP) output.prelude_imp
      }

      for (axm <- theory.axioms) {
        if (verbose) progress.echo("  " + axm.entity.toString)

        output.stmt_decl(LP_Syntax.axiom_kind(axm.entity.name), axm.prop, None)
      }

      for (thm <- theory.thms) {
        if (verbose) progress.echo("  " + thm.entity.toString)

        val boxes =
          try {
            Export_Theory.read_proof_boxes(
              store, provider, thm.proof,
              suppress = id => exported_proofs(id.serial), cache = Some(cache))
          }
          catch { case ERROR(msg) => error(msg + "\nin " + thm.entity) }

        for ((id, prf) <- boxes) {
          if (verbose) {
            progress.echo("  proof " + id.serial +
              (if (theory.name == id.theory_name) "" else " (from " + id.theory_name + ")"))
          }

          exported_proofs += id.serial
          output.proof_decl(id.serial, prf.prop, prf.proof)
        }
        output.stmt_decl(LP_Syntax.thm_kind(thm.entity.name), thm.prop, Some(thm.proof))
      }
    }

    def theory_file(theory_name: String) =
      output_file.dir + Path.explode(theory_name + ".lp")


    /* import session (headless PIDE) */

    val sessions = context.sessions(logic)

    if (sessions.isEmpty) {
      progress.echo_warning("Nothing to import")
    }
    else {
      var imported_theories = new ListBuffer[String]

      using(new LP_Syntax.Output(theory_file(Thy_Header.PURE)))(output =>
      {
        output.prelude_eta
        output.prelude_type

        import_theory(
          output,
          Export_Theory.read_pure_theory(store, cache = Some(cache)),
          Export.Provider.none)
        imported_theories += Thy_Header.PURE
      })

      sessions.foreach(_.process((args: Dump.Args) =>
        {
          val snapshot = args.snapshot
          val provider = Export.Provider.snapshot(snapshot)
          val theory_name = snapshot.node_name.theory
          val theory =
            Export_Theory.read_theory(provider, Sessions.DRAFT, theory_name, cache = Some(cache))

          using(new LP_Syntax.Output(theory_file(theory.name)))(output =>
          {
            output.prelude_eta

            for {
              name <- snapshot.version.nodes.requirements(List(snapshot.node_name))
              if name.is_theory && name.theory != theory_name
            } output.require_open(name.theory)

            import_theory(output, theory, provider)
            imported_theories += theory.name
          })

        }))

      using(new LP_Syntax.Output(output_file))(output =>
        imported_theories.foreach(output.require_open))
    }

    context.check_errors

    progress.echo("Output " + output_file)
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", args =>
    {
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var output_file = default_output_file
      var requirements = false
      var exclude_session_groups: List[String] = Nil
      var all_sessions = false
      var dirs: List[Path] = Nil
      var session_groups: List[String] = Nil
      var options = Options.init()
      var verbose = false
      var exclude_sessions: List[String] = Nil

      val getopts = Getopts("""
Usage: isabelle dedukti_import [OPTIONS] [SESSIONS ...]

  Options are:
    -B NAME      include session NAME and all descendants
    -D DIR       include session directory and select its sessions
    -O FILE      output file for Dedukti theory in lp syntax (default: """ + default_output_file + """)
    -R           operate on requirements of selected sessions
    -X NAME      exclude sessions from group NAME and all descendants
    -a           select all sessions
    -d DIR       include session directory
    -g NAME      select session group NAME
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode
    -x NAME      exclude session NAME and all descendants

  Import specified sessions as Dedukti files.
""",
      "B:" -> (arg => base_sessions = base_sessions ::: List(arg)),
      "D:" -> (arg => { select_dirs = select_dirs ::: List(Path.explode(arg)) }),
      "R" -> (_ => requirements = true),
      "O:" -> (arg => output_file = Path.explode(arg)),
      "X:" -> (arg => exclude_session_groups = exclude_session_groups ::: List(arg)),
      "a" -> (_ => all_sessions = true),
      "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
      "g:" -> (arg => session_groups = session_groups ::: List(arg)),
      "o:" -> (arg => { options += arg }),
      "v" -> (_ => verbose = true),
      "x:" -> (arg => exclude_sessions = exclude_sessions ::: List(arg)))

      val sessions = getopts(args)

      val selection =
        Sessions.Selection(
          requirements = requirements,
          all_sessions = all_sessions,
          base_sessions = base_sessions,
          exclude_session_groups = exclude_session_groups,
          exclude_sessions = exclude_sessions,
          session_groups = session_groups,
          sessions = sessions)

      val progress =
        new Console_Progress(verbose = verbose) {
          override def theory(theory: Progress.Theory): Unit =
            if (verbose) echo("Processing " + theory.print_theory + theory.print_percentage)
        }

      val start_date = Date.now()
      if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

      progress.interrupt_handler {
        try {
          importer(options,
            progress = progress,
            dirs = dirs,
            select_dirs = select_dirs,
            selection = selection,
            output_file = output_file,
            verbose = verbose)
        }
        finally {
          val end_date = Date.now()
          if (verbose) progress.echo("\nFinished at " + Build_Log.print_date(end_date))
          progress.echo((end_date.time - start_date.time).message_hms + " elapsed time")
        }
      }
    }
  )
}
