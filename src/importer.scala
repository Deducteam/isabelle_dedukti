/** Isabelle/Dedukti importer (lp syntax) **/


package isabelle.dedukti

import isabelle._


object Importer
{
  /* importer */

  val default_output_file: Path = Path.explode("output.lp")

  def importer(
    options: Options,
    session: String,
    progress: Progress = No_Progress,
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    output_file: Path = default_output_file,
    verbose: Boolean = false)
  {
    /* build session with exports */

    val build_options =
    {
      val options1 = options + "export_theory" + "record_proofs=2"
      if (options.bool("export_standard_proofs")) options1 + "prune_proofs=false"
      else options1 + "export_proofs" + "prune_proofs=false" // FIXME
    }

    Build.build_logic(build_options, session, progress = progress, dirs = dirs,
      fresh = fresh_build, strict = true)


    /* session structure */

    val base_info = Sessions.base_info(options, Thy_Header.PURE, progress = progress, dirs = dirs)

    val session_info =
      base_info.sessions_structure.get(session) match {
        case Some(info) if info.parent == Some(Thy_Header.PURE) => info
        case Some(_) => error("Parent session needs to be Pure")
        case None => error("Bad session " + quote(session))
      }

    val resources = new Resources(base_info.sessions_structure, base_info.check_base)

    val dependencies = resources.session_dependencies(session_info, progress = progress)


    /* import theory content */

    val store = Sessions.store(options)
    val cache = Term.make_cache()

    var exported_proofs = Set.empty[Long]

    def import_theory(
      output: Syntax.SyntaxWriter,
      theory: Export_Theory.Theory,
      provider: Export.Provider)
    {
      progress.echo("Importing theory " + theory.name)

      //output.string("\n\n// theory " + theory.name + "\n\n")

      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.entity.toString)
        output.write(Translate.class_decl(a.entity.name))
      }

      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.entity.toString)

        a.abbrev match {
          case None => output.write(Translate.type_decl(a.entity.name, a.args.length))
          case Some(rhs) => output.write(Translate.type_abbrev(a.entity.name, a.args, rhs))
        }

        if (a.entity.name == Pure_Thy.FUN ) output.write(Prelude.funR)
        if (a.entity.name == Pure_Thy.PROP) output.write(Prelude.epsD)
      }

      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.entity.toString)

        a.abbrev match {
          case None => output.write(Translate.const_decl(a.entity.name, a.typargs, a.typ))
          case Some(rhs) => output.write(Translate.const_abbrev(a.entity.name, a.typargs, a.typ, rhs))
        }

        if (a.entity.name == Pure_Thy.ALL) output.write(Prelude.allR)
        if (a.entity.name == Pure_Thy.IMP) output.write(Prelude.impR)
      }

      for (axm <- theory.axioms) {
        if (verbose) progress.echo("  " + axm.entity.toString)

        output.write(Translate.stmt_decl(Prelude.axiom_kind(axm.entity.name), axm.prop, None))
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
          output.write(Translate.proof_decl(id.serial, prf.prop, prf.proof))
        }
        output.write(Translate.stmt_decl(Prelude.thm_kind(thm.entity.name), thm.prop, Some(thm.proof)))
      }
    }


    def theory_file(theory_name: String) =
      output_file.dir + Path.explode(theory_name + ".lp")


    /* import session */

    val all_theories = dependencies.theory_graph.topological_order

    using(store.open_database(session))(db =>
    {
      for (name <- all_theories) {
        using(new PartWriter(theory_file(name.theory)))(partwriter =>
        {
          partwriter.write("""set flag "eta_equality" on""" + "\n")

          val syntax = new LP_Syntax.SyntaxWriter(partwriter)

          if (name.theory == Thy_Header.PURE) {
            syntax.write(Prelude.typeD)
            syntax.write(Prelude.etaD)

            import_theory(syntax,
              Export_Theory.read_pure_theory(store, cache = Some(cache)),
              Export.Provider.none)
          }
          else {
            val provider = Export.Provider.database(db, session, name.theory)
            val theory =
              Export_Theory.read_theory(provider, session, name.theory, cache = Some(cache))

            for {
              req <- dependencies.theory_graph.all_preds(List(name)).reverse.map(_.theory)
              if req != name.theory
            } syntax.require_open(req)
    
            import_theory(syntax, theory, provider)
          }
        })
      }
    })

    using(new PartWriter(output_file))(output => {
      val syntax = new LP_Syntax.SyntaxWriter(output)
      all_theories.foreach(name => syntax.require_open(name.theory))
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", args =>
    {
      var output_file = default_output_file
      var dirs: List[Path] = Nil
      var fresh_build = false
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle dedukti_import [OPTIONS] SESSION

  Options are:
    -O FILE      output file for Dedukti theory in lp syntax (default: """ + default_output_file + """)
    -d DIR       include session directory
    -f           fresh build
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

  Import specified sessions as Dedukti files.
""",
      "O:" -> (arg => output_file = Path.explode(arg)),
      "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
      "f" -> (_ => fresh_build = true),
      "o:" -> (arg => { options += arg }),
      "v" -> (_ => verbose = true))

      val more_args = getopts(args)

      val session =
        more_args match {
          case List(name) => name
          case _ => getopts.usage()
        }

      val progress = new Console_Progress(verbose = true)

      val start_date = Date.now()
      if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

      progress.interrupt_handler {
        try {
          importer(options, session,
            progress = progress,
            dirs = dirs,
            fresh_build = fresh_build,
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
