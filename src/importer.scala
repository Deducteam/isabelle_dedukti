/** Isabelle/Dedukti importer **/


package isabelle.dedukti

import isabelle._


object Importer
{
  /* importer */

  val default_output_file: Path = Path.explode("main.lp")

  def importer(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    use_notations: Boolean = false,
    output_file: Path = default_output_file,
    verbose: Boolean = false)
  {
    /* build session with exports */

    val build_options =
    {
      val options1 = options + "export_theory" + "record_proofs=2"
      if (options.bool("export_standard_proofs")) options1
      else options1 + "export_proofs"
    }

    Build.build_logic(build_options, session, progress = progress, dirs = dirs,
      fresh = fresh_build, strict = true)


    /* session structure */

    val base_info = Sessions.base_info(options, Thy_Header.PURE, progress = progress, dirs = dirs)

    val session_info =
      base_info.sessions_structure.get(session) match {
        case Some(info) if info.parent.contains(Thy_Header.PURE) => info
        case Some(_) => error("Parent session needs to be Pure")
        case None => error("Bad session " + quote(session))
      }

    val resources = new Resources(base_info.sessions_structure, base_info.check.base)

    val dependencies = resources.session_dependencies(session_info, progress = progress)


    /* import theory content */

    val store = Sessions.store(options)
    val term_cache = Term.Cache.make()

    var exported_proofs = Set.empty[Long]

    def proof_boxes(thm: Export_Theory.Entity[Export_Theory.Thm], provider: Export.Provider)
      : List[(Export_Theory.Thm_Id, Export_Theory.Proof)] =
    {
      try {
        Export_Theory.read_proof_boxes(
          store, provider, thm.the_content.proof,
          suppress = id => exported_proofs(id.serial), cache = term_cache)
      }
      catch { case ERROR(msg) => error(msg + "\nin " + thm) }
    }

    def import_theory(
      output: Abstract_Writer,
      notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation],
      theory: Export_Theory.Theory,
      provider: Export.Provider): Unit =
    {
      progress.echo("Importing theory " + theory.name)

      output.nl()
      output.comment("theory " + theory.name)
      output.nl()

      if (theory.name == Thy_Header.PURE) {
        output.command(Prelude.typeD, notations)
        output.command(Prelude.etaD, notations)
      }

      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.toString)
        output.command(Translate.class_decl(a.name), notations)
      }

      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString)
        output.command(Translate.type_decl(a.name, a.args, a.abbrev, a.syntax), notations)

        if (a.name == Pure_Thy.FUN ) {
          output.command(Prelude.funR, notations)
        }
        if (a.name == Pure_Thy.PROP) {
          output.command(Prelude.epsD, notations)
        }
      }

      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString)
        output.command(Translate.const_decl(a.name, a.typargs, a.typ, a.abbrev, a.syntax), notations)

        if (a.name == Pure_Thy.ALL) {
          output.command(Prelude.allR, notations)
        }
        if (a.name == Pure_Thy.IMP) {
          output.command(Prelude.impR, notations);
        }
      }

      for (axm <- theory.axioms) {
        if (verbose) progress.echo("  " + axm.toString)
        output.command(Translate.stmt_decl(Prelude.axiom_ident(axm.name), axm.the_content.prop, None), notations)
      }

      for (thm <- theory.thms) {
        if (verbose) progress.echo("  " + thm.toString)

        for ((id, prf) <- proof_boxes(thm, provider)) {
          if (verbose) {
            progress.echo("  proof " + id.serial +
              (if (theory.name == id.theory_name) "" else " (from " + id.theory_name + ")"))
          }

          exported_proofs += id.serial
          output.command(Translate.stmt_decl(Prelude.proof_ident(id.serial), prf.prop, Some(prf.proof)), notations)
        }
        output.command(Translate.stmt_decl(Prelude.thm_ident(thm.name),
          thm.the_content.prop, Some(thm.the_content.proof)), notations)
      }
    }


    /* import session */

    val all_theories = dependencies.theory_graph.topological_order

    using(store.open_database(session))(db =>
    {
      def import_theory_by_name(name: String, syntax: Abstract_Writer, notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation]): Unit =
      {
        if (name == Thy_Header.PURE) {
          import_theory(syntax, notations,
            Export_Theory.read_pure_theory(store, cache = term_cache),
            Export.Provider.none)
        }
        else {
          val provider = Export.Provider.database(db, store.cache, session, name)
          val theory = Export_Theory.read_theory(provider, session, name, cache = term_cache)

          import_theory(syntax, notations, theory, provider)
        }
      }
      val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()

      val ext = output_file.get_ext
      ext match {
        case "dk" =>
          // write into a single file
          using(new Part_Writer(output_file))(writer =>
          {
            val syntax = new DK_Writer(writer)
            for (name <- all_theories)
              import_theory_by_name(name.theory, syntax, notations)
          })

        case "lp" =>
          def theory_file(theory_name: String): Path =
            output_file.dir + Path.explode(theory_name + ".lp")

          // write one file per theory
          for (name <- all_theories) {
            using(new Part_Writer(theory_file(name.theory)))(writer =>
            {
              val syntax = new LP_Writer(output_file.dir, use_notations, writer)
              syntax.eta_equality()

              for {
                req <- dependencies.theory_graph.all_preds(List(name)).reverse.map(_.theory)
                if req != name.theory
              } syntax.require_open(req)

              import_theory_by_name(name.theory, syntax, notations)
            })
          }

          // write one file that loads all the other ones
          using(new Part_Writer(output_file))(output =>
          {
            val syntax = new LP_Writer(output_file.dir, use_notations, output)
            all_theories.foreach(name => syntax.require_open(name.theory))
          })

        case ext => error("Unknown output format " + ext)
      }
    })
  }


  /* Isabelle tool wrapper */

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", Scala_Project.here,
      args =>
    {
      var output_file = default_output_file
      var dirs: List[Path] = Nil
      var fresh_build = false
      var use_notations = false
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle dedukti_import [OPTIONS] SESSION

  Options are:
    -O FILE      output file for Dedukti theory in dk or lp syntax (default: """ + default_output_file + """)
    -d DIR       include session directory
    -f           fresh build
    -n           use lambdapi notations
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

  Import specified sessions as Dedukti files.
""",
      "O:" -> (arg => output_file = Path.explode(arg)),
      "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
      "f" -> (_ => fresh_build = true),
      "n" -> (_ => use_notations = true),
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
            use_notations = use_notations,
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
