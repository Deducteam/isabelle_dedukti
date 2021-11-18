/** Isabelle/Dedukti importer **/


package isabelle.dedukti

import isabelle._

import scala.collection.mutable

object Importer
{
  /* importer */

  val default_output_file: Path = Path.explode("main.lp")

  // Main function called by the CLI handler
  def importer(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    output_file: Path = default_output_file,
    verbose: Boolean = false) : Unit =
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

    def translate_theory(
      theory: Export_Theory.Theory,
      provider: Export.Provider,
      previous_theories: Map[String, mutable.Queue[Syntax.Command]])
        : Map[String, mutable.Queue[Syntax.Command]] = {
      progress.echo("Translating theory " + theory.name)

      val current_theories = {
        if (previous_theories contains theory.name)
          previous_theories
        else
          previous_theories + (theory.name -> mutable.Queue[Syntax.Command]())
      }
      val current_theory = current_theories(theory.name)

      if (theory.name == Thy_Header.PURE) {
        current_theory.append(Prelude.typeD)
        current_theory.append(Prelude.etaD)
      }

      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.toString)
        output.write(Translate.class_decl(a.name))
      }

      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString)
        output.write(Translate.type_decl(a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))

        if (a.name == Pure_Thy.FUN ) output.write(Prelude.funR)
        if (a.name == Pure_Thy.PROP) output.write(Prelude.epsD)
      }

      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString)
        output.write(Translate.const_decl(a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))

        if (a.name == Pure_Thy.ALL) output.write(Prelude.allR)
        if (a.name == Pure_Thy.IMP) output.write(Prelude.impR)
      }

      for (axm <- theory.axioms) {
        if (verbose) progress.echo("  " + axm.toString)
        output.write(Translate.stmt_decl(Prelude.axiom_kind(axm.name), axm.the_content.prop, None))
      }

      for (thm <- theory.thms) {
        if (verbose) progress.echo("  " + thm.toString)

        for ((id, prf) <- proof_boxes(thm, provider)) {
          if (verbose) {
            progress.echo("  proof " + id.serial +
              (if (theory.name == id.theory_name) "" else " (from " + id.theory_name + ")"))
          }

          exported_proofs += id.serial
          current_theories(id.theory_name).append(Translate.stmt_decl(Prelude.proof_ident(id.serial), prf.prop, Some(prf.proof)))
        }
        output.write(Translate.stmt_decl(Prelude.thm_kind(thm.name), thm.the_content.prop, Some(thm.the_content.proof)))
      }
      current_theories
    }


    def write_theory(
      theory_name: String,
      output: Abstract_Writer,
      notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation],
      theory: List[Syntax.Command]): Unit =
    {
      progress.echo("Writing theory " + theory_name)

      output.comment("theory " + theory_name)
      output.nl()

      for (command <- theory) {
        output.command(command, notations)
      }
    }


    /* import session */

    val all_theories = dependencies.theory_graph.topological_order

    using(store.open_database(session))(db =>
    {
      def translate_theory_by_name(name: String, previous_theories: Map[String, mutable.Queue[Syntax.Command]]): Map[String, mutable.Queue[Syntax.Command]] = {
        if (name == Thy_Header.PURE) {
          translate_theory(Export_Theory.read_pure_theory(store, cache = term_cache),
            Export.Provider.none, previous_theories)
        }
        else {
          val provider = Export.Provider.database(db, store.cache, session, name)
          val theory = Export_Theory.read_theory(provider, session, name, cache = term_cache)

          translate_theory(theory, provider, previous_theories)
        }
      }

      Translate.global_eta_expand = eta_expand
      
      val translated_theories =
        all_theories
          .foldLeft(Map[String, mutable.Queue[Syntax.Command]]())((n, m) => translate_theory_by_name(m.theory, n))
          .view.mapValues(_.toList).toMap

      val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()

      val ext = output_file.get_ext
      ext match {
        case "dk" =>
          // write into a single file
          using(new Part_Writer(output_file))(writer =>
          {
            val syntax = new DK_Writer(writer)
            for (name <- all_theories)
              write_theory(name.theory, syntax, notations, translated_theories(name.theory))
          })

        case "lp" =>
          def theory_file(theory_name: String): Path =
            output_file.dir + Path.explode(theory_name + ".lp")

          // write one file per theory
          for (name <- all_theories) {
            using(new Part_Writer(theory_file(name.theory)))(writer =>
            {
              val syntax = new LP_Writer(output_file.dir, use_notations, writer)
              if (!eta_expand) syntax.eta_equality()

              for {
                req <- dependencies.theory_graph.all_preds(List(name)).reverse.map(_.theory)
                if req != name.theory
              } syntax.require_open(req)

              write_theory(name.theory, syntax, notations, translated_theories(name.theory))
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


  /* Isabelle tool wrapper and CLI handler */

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", Scala_Project.here,
      args =>
    {
      var output_file = default_output_file
      var dirs: List[Path] = Nil
      var fresh_build = false
      var use_notations = false
      var eta_expand = false
      var options = Options.init()
      var verbose = false

      val getopts = Getopts("""
Usage: isabelle dedukti_import [OPTIONS] SESSION

  Options are:
    -O FILE      output file for Dedukti theory in dk or lp syntax (default: """ + default_output_file + """)
    -d DIR       include session directory
    -f           fresh build
    -n           use lambdapi notations
    -e           remove need for eta flag
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

  Import specified sessions as Dedukti files.
""",
      "O:" -> (arg => output_file = Path.explode(arg)),
      "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
      "f" -> (_ => fresh_build = true),
      "e" -> (_ => eta_expand = true),
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
            eta_expand = eta_expand,
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
