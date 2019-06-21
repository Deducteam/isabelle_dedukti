package isabelle.dedukti

import isabelle._

object Dedukti
{
  /* importer */

  val default_output_dir: Path = Path.explode("dedukti")

  def importer(
    options: Options,
    progress: Progress = No_Progress,
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output_dir: Path = default_output_dir,
    selection: Sessions.Selection = Sessions.Selection.empty)
  {
    val dump_options: Options = Dump.make_options(options, Dump.known_aspects)

    val session_deps =
      Dump.dependencies(dump_options, progress = progress,
        dirs = dirs, select_dirs = select_dirs, selection = selection)

    val resources: Headless.Resources =
      Headless.Resources.make(dump_options, Thy_Header.PURE, progress = progress,
        session_dirs = dirs ::: select_dirs,
        include_sessions = session_deps.sessions_structure.imports_topological_order)

    val import_theories = resources.used_theories(session_deps, progress = progress)

    if (session_deps.is_empty) {
      progress.echo_warning("Nothing to import")
    }
    else {
      progress.echo("Theories to import:")
      for (node_name <- import_theories) progress.echo("  " + node_name.toString)
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", args =>
    {
      var base_sessions: List[String] = Nil
      var select_dirs: List[Path] = Nil
      var output_dir = default_output_dir
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
    -O DIR       output directory for Dedukti files (default: """ + default_output_dir + """)
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
      "O:" -> (arg => output_dir = Path.explode(arg)),
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
            output_dir = output_dir)
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
