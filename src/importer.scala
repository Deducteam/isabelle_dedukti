/** Isabelle/Dedukti importer (lp syntax) **/


package isabelle.dedukti

import isabelle._

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

    val context =
      Dump.Context(options + "record_proofs=2" + "export_proofs" + "prune_proofs",
        aspects = Dump.known_aspects, progress = progress,
        dirs = dirs, select_dirs = select_dirs, selection = selection)

    context.build_logic(logic)

    using(new LP_Syntax.Output(output_file))(output =>
    {
      /* import theory content */

      def import_theory(
        theory: Export_Theory.Theory,
        read_proof: Export_Theory.Thm_Id => Option[Export_Theory.Proof])
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

          output.stmt_decl(axm.entity.name, axm.prop, axm.entity.kind)
        }

        for (thm <- theory.thms) {
          if (verbose) progress.echo("  " + thm.entity.toString)

          for (id <- thm.proof_boxes) output.proof_decl(id, read_proof)
          output.stmt_decl(thm.entity.name, thm.prop, thm.entity.kind)
        }
      }


      /* import session (headless PIDE) */

      val sessions = context.sessions(logic)

      if (sessions.isEmpty) {
        progress.echo_warning("Nothing to import")
      }
      else {
        output.prelude_type

        import_theory(
          Export_Theory.read_pure_theory(store, cache = Some(cache)),
          Export_Theory.read_pure_proof(store, _, cache = Some(cache)))

        sessions.foreach(_.process((args: Dump.Args) =>
          {
            val snapshot = args.snapshot
            val provider = Export.Provider.snapshot(snapshot)
            val theory_name = snapshot.node_name.theory
            val theory =
              Export_Theory.read_theory(provider, Sessions.DRAFT, theory_name, cache = Some(cache))

            def read_proof(id: Export_Theory.Thm_Id): Option[Export_Theory.Proof] =
            {
              val proof =
                if (id.pure) Export_Theory.read_pure_proof(store, id, cache = Some(cache))
                else Export_Theory.read_proof(provider, id, cache = Some(cache))

              if (verbose && proof.isDefined) {
                progress.echo("  proof " + id.serial +
                  (if (theory_name == id.theory_name) "" else " (from " + id.theory_name + ")"))
              }
              proof
            }

            import_theory(theory, read_proof)
          }))
      }

      context.check_errors
    })

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
