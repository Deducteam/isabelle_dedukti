/** Isabelle/Dedukti importer **/


package isabelle.dedukti

import isabelle._

import scala.collection.mutable


object Importer {
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
    verbose: Boolean = false
  ): Unit = {
    /* build session with exports */

    val build_options = {
      val options1 = options + "export_theory" + "record_proofs=2"
      if (options.bool("export_standard_proofs")) options1
      else options1 + "export_proofs"
    }

    Build.build_logic(build_options, session, progress = progress, dirs = dirs,
      fresh = fresh_build, strict = true)


    /* session structure */
    val full_sessions = Sessions.load_structure(options, dirs = dirs)
    val base_info = Sessions.base_info(options, "Pure", progress = progress, dirs = dirs)
    val session_info =
      base_info.sessions_structure.get(session) match {
        case Some(info) => info
        case None => error("Bad session " + quote(session))
      }
    val resources = new Resources(base_info.sessions_structure, base_info.check.base)

    val whole_graph =
      if (session == "Pure") {
        (Document.Node.Name.make_graph(List(((Document.Node.Name("Pure", theory = "Pure"), ()),List[Document.Node.Name]()))))
      } else {
        resources.session_dependencies(session_info, progress = progress).theory_graph
      }
    val all_theories : List[Document.Node.Name] = whole_graph.topological_order

    progress.echo("Whole graph: " + whole_graph)
    progress.echo("all_theories: " + all_theories)

    /* import theory content */

    val store = Sessions.store(options)
    val term_cache = Term.Cache.make()
    val db = store.open_database(session)
    progress.echo("DB: " + db)

    def decode_proof : XML.Decode.T[Export_Theory.Proof] = {
    import XML.Decode._
    variant(List(
      { case (_,body) =>
        val (typargs, (args, (prop_body, proof_body))) =
        {
          import XML.Decode._
          import Term_XML.Decode._
          pair(list(pair(string, sort)), pair(list(pair(string, typ)), pair(x => x, x => x)))(body)
        }
        val env = args.toMap
        val prop = Term_XML.Decode.term_env(env)(prop_body)
        val proof = Term_XML.Decode.proof_env(env)(proof_body)
        
        val result = Export_Theory.Proof(typargs, args, prop, proof)
        if (term_cache.no_cache) result else result.cache(term_cache)
      }
    ))
    }

    var exported_proofs = Set.empty[Long]

    /*def proof_boxes(
      thm: Export_Theory.Entity[Export_Theory.Thm],
      provider: Export.Provider
    ) : List[(Export_Theory.Thm_Id, Export_Theory.Proof)] = {
      try {
        Export_Theory.read_proof_boxes(
          store, provider, thm.the_content.proof,
          suppress = id => exported_proofs(id.serial), cache = term_cache)
      }
      catch { case ERROR(msg) => error(msg + "\nin " + thm) }
    }*/

    def translate_theory(
      theory: Export_Theory.Theory,
      previous_theories: Map[String, mutable.Queue[Syntax.Command]],
      with_prf : Boolean )
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
        if (verbose) progress.echo("  " + a.toString + a.serial)
        current_theory.append(Translate.class_decl(a.name))
      }

      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        current_theory.append(Translate.type_decl(a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))

        if (a.name == Pure_Thy.FUN ) {
          current_theory.append(Prelude.funR)
        }
        if (a.name == Pure_Thy.PROP) {
          current_theory.append(Prelude.epsD)
        }
      }

      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        current_theory.append(Translate.const_decl(a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))

        if (a.name == Pure_Thy.ALL) {
          current_theory.append(Prelude.allR)
        }
        if (a.name == Pure_Thy.IMP) {
          current_theory.append(Prelude.impR);
        }
      }

      for (axm <- theory.axioms) {
        if (verbose) progress.echo("  " + axm.toString + " " + axm.serial)
        current_theory.append(Translate.stmt_decl(Prelude.axiom_ident(axm.name), axm.the_content.prop, None))
      }

      val provider = Export.Provider.database(db, store.cache, session, theory.name)
      def get_thm_prf(thm : Export_Theory.Entity[Export_Theory.Thm]) = {
        def sub(p:Term.Proof) : Long = p match {
          case Term.PThm(thm_prf,_,_,_) => thm_prf
          case Term.Appt(p,t) => sub(p)
          case Term.AppP(p,q) => Math.max(sub(p), sub(q))
          case Term.Abst(x, ty, b) => sub(b)
          case Term.AbsP(x, hyp, b) => sub(b)
          case _ => 0
        }
        sub(thm.the_content.proof)
        }
      def translate_thm(thm : Export_Theory.Entity[Export_Theory.Thm]) = {
        if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
        current_theory.append(Translate.stmt_decl(Prelude.thm_ident(thm.name),
        thm.the_content.prop, if (with_prf) Some(thm.the_content.proof) else None))
      }

      def prf_loop(prfs : List[Long], thm : Export_Theory.Entity[Export_Theory.Thm], thms : List[Export_Theory.Entity[Export_Theory.Thm]],thm_prf : Long) : Unit = prfs match {
        case prf_serial::prfs2 =>
          if (prf_serial > thm_prf) {
            // progress.echo("  Ready for thm " + prf_serial + " > " + thm_prf)
            translate_thm(thm)
            thms match {
              case thm2 :: thms2 =>
              prf_loop(prfs,thm2,thms2,get_thm_prf(thm2))
              case Nil =>
              prf_loop(prfs,null,null,Long.MaxValue)
            }
          } else {
            val prf_id = Export_Theory.Thm_Id(prf_serial,theory.name)
            // if (verbose) {
            // progress.echo("  proof " + prf_serial )
            // }
            val prf = Export_Theory.read_proof(provider, prf_id, cache = term_cache) match {
              case Some(prf) => prf
            }
            current_theory.append(Translate.stmt_decl(Prelude.proof_ident(prf_serial), prf.prop, if (with_prf) Some(prf.proof) else None))
            prf_loop(prfs2,thm,thms,thm_prf)
          }
        case _ =>
      }
      val exports = Export.read_theory_exports(db,session)
      val prfs = exports.foldLeft(Nil: List[Long]) {
        case (prfs2 : List[Long],(thy_name,prf_name)) => (
          if (thy_name == theory.name && prf_name.startsWith("proofs/")) {
            prf_name.substring(7).toLong :: prfs2
          } else {
            // if (thy_name == "HOL.Groups" && theory.name == "HOL.Lattices" && prf_name.startsWith("proofs/")) {
            //   progress.echo("We found a proof " + prf_name + " from the wrong theory " + thy_name + " compared to " + theory.name)
            //   val prf_id = Export_Theory.Thm_Id(prf_name.substring(7).toLong,thy_name)
            //   val prf = Export_Theory.read_proof(provider, prf_id, cache = term_cache) match {
            //     case Some(prf) => prf
            //   }
            //   progress.echo("It has the following statement:" + prf.prop)
            // }
            prfs2
          }
        )
      }
      theory.thms match {
        case thm :: thms => prf_loop(prfs.sorted,thm,thms,get_thm_prf(thm))
        case _ => prf_loop(prfs.sorted,null,null,Long.MaxValue)
      }
      // for (item <- current_theory) {
      //   item match {
      //     case Syntax.Theorem(x,_,_,_) /*if (x == 187462)*/ => progress.echo("Found the item: " + item)
      //     case _ => 
      //   }
      // }
      
      current_theories
    }


    def write_theory(
      theory_name: String,
      output: Abstract_Writer,
      notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation],
      theory: List[Syntax.Command]
    ): Unit = {
      progress.echo("Writing theory " + theory_name)

      output.comment("theory " + theory_name)
      output.nl()

      for (command <- theory) {
        output.command(command, notations)
      }
    }


    // gets provider for the thy
    def get_theory(sessionn: String, thy_name: String) : (Export_Theory.Theory, String) = {
      if (thy_name == Thy_Header.PURE) {
        (Export_Theory.read_pure_theory(store, cache = term_cache), "Pure")
      } else {
        try {
          val db = store.open_database(sessionn)
          val provider = Export.Provider.database(db, store.cache, sessionn, thy_name)
          (Export_Theory.read_theory(provider, sessionn, thy_name, cache = term_cache), sessionn)
        } catch {
          case _ : Throwable =>
          full_sessions(sessionn).parent match {
            case Some(parent) => get_theory(parent,thy_name)
            case None => error("Bad session " + quote(sessionn))
          }
        }
      }
    }

      def translate_theory_by_name(name: String, previous_theories: Map[String, mutable.Queue[Syntax.Command]]): Map[String, mutable.Queue[Syntax.Command]] = {
        val (theory,sess) = get_theory(session,name)
        translate_theory(theory, previous_theories, sess == session)
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
          using(new Part_Writer(output_file)) { writer =>
            val syntax = new DK_Writer(writer)
            for (name <- all_theories)
              write_theory(name.theory, syntax, notations, translated_theories(name.theory))
          }

        case "lp" =>
          def theory_file(theory_name: String): Path =
            output_file.dir + Path.explode(theory_name + ".lp")

          // write one file per theory
          for (name <- all_theories) {
            val (_, sess) = get_theory(session, name.toString)
            if (sess == session) {
              using(new Part_Writer(theory_file(name.theory))) { writer =>
                val syntax = new LP_Writer(output_file.dir, use_notations, writer)
                if (!eta_expand) syntax.eta_equality()

                for {
                  req <- whole_graph.all_preds(List(name)).reverse.map(_.theory)
                  if req != name.theory
                } syntax.require_open(req)

                write_theory(name.theory, syntax, notations, translated_theories(name.theory))
              }
            }
          }

          // write one file that loads all the other ones
          using(new Part_Writer(output_file)) { output =>
            val syntax = new LP_Writer(output_file.dir, use_notations, output)
            all_theories.foreach(name => syntax.require_open(name.theory))
          }

        case ext => error("Unknown output format " + ext)
      }
  }


  /* Isabelle tool wrapper and CLI handler */

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("dedukti_import", "import theory content into Dedukti", Scala_Project.here,
      { args =>
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
          catch {case x: Exception =>
            progress.echo(x.getStackTrace.mkString("\n"))
            println(x)}
          finally {
            val end_date = Date.now()
            if (verbose) progress.echo("\nFinished at " + Build_Log.print_date(end_date))
            progress.echo((end_date.time - start_date.time).message_hms + " elapsed time")
          }
        }
      })
}
