/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle._

import scala.collection.mutable
import scala.util.control.Breaks._

object Exporter {

  def exporter(
    options: Options,
    session: String,
    theory_name: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    output_lp: Boolean = false,
    verbose: Boolean = false
  ): Unit = {

    // to generate qualified identifiers
    Prelude.set_current_module(theory_name)

    progress.echo("Read theory " + theory_name + " ...")

    val build_options = {
      val options1 = options + "export_theory" + "record_proofs=2"
      if (options.bool("export_standard_proofs")) options1
      else options1 + "export_proofs"
    }
    Build.build_logic(build_options, session, progress = progress, dirs = dirs,
      fresh = fresh_build, strict = true)

    val store = Sessions.store(options)
    val term_cache = Term.Cache.make()
    val db = store.open_database(session)
    //progress.echo("DB: " + db)
    val provider = Export.Provider.database(db, store.cache, session, theory_name)

    val theory =
      if (theory_name == Thy_Header.PURE) {
        Export_Theory.read_pure_theory(store, cache = term_cache)
      } else {
        Export_Theory.read_theory(provider, session, theory_name, cache = term_cache)
      }

    progress.echo("Translate theory " + theory_name + " ...")

    val current_theory = mutable.Queue[Syntax.Command]()
    for (a <- theory.classes) {
      // if (verbose) progress.echo("  " + a.toString + a.serial)
      current_theory.append(Translate.class_decl(a.name))
    }
    for (a <- theory.types) {
      // if (verbose) progress.echo("  " + a.toString + a.serial)
      current_theory.append(Translate.type_decl(a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))
    }
    for (a <- theory.consts) {
      // if (verbose) progress.echo("  " + a.toString + " " + a.serial)
      current_theory.append(Translate.const_decl(a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))
    }
    for (a <- theory.axioms) {
      // if (verbose) progress.echo("  " + axm.toString + " " + axm.serial)
      current_theory.append(Translate.stmt_decl(Prelude.axiom_ident(a.name), a.the_content.prop, None))
    }

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
      // if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
      current_theory.append(Translate.stmt_decl(Prelude.thm_ident(thm.name), thm.the_content.prop, Some(thm.the_content.proof)))
    }

    def prf_loop(prfs : List[(Long,Export_Theory.Proof)], thm : Export_Theory.Entity[Export_Theory.Thm], thms : List[Export_Theory.Entity[Export_Theory.Thm]],thm_prf : Long) : Unit = prfs match {
      case (prf_serial,prf)::prfs2 =>
        if (prf_serial > thm_prf) {
          translate_thm(thm)
          // progress.echo("  Ready for thm " + prf_serial + " > " + thm_prf)
          thms match {
            case thm2 :: thms2 =>
            prf_loop(prfs,thm2,thms2,get_thm_prf(thm2))
            case Nil =>
            prf_loop(prfs,null,null,Long.MaxValue)
          }
        } else {
          // if (verbose) progress.echo("  proof " + prf_serial)
          current_theory.append(Translate.stmt_decl(Prelude.proof_ident(prf_serial), prf.prop, Some(prf.proof)))
          prf_loop(prfs2,thm,thms,thm_prf)
        }
      case _ =>
    }
    val exports = Export.read_theory_exports(db,session)
    val prfs = 
      exports.foldLeft(Nil: List[(Long,Export_Theory.Proof)]) {
        case (prfs2 : List[(Long,Export_Theory.Proof)],(thy_name,prf_name)) => (
          if (prf_name.startsWith("proofs/")) {
            val prf_serial = prf_name.substring(7).toLong
            Export_Theory.read_proof(provider, Export_Theory.Thm_Id(prf_serial,thy_name), cache = term_cache) match {
              case Some(prf) => (prf_serial,prf)::prfs2
              case None => prfs2
            }
          } else { prfs2 }
        )
      }
    theory.thms match {
      case thm :: thms => prf_loop(prfs.sortBy(_._1),thm,thms,get_thm_prf(thm))
      case _ => prf_loop(prfs.sortBy(_._1),null,null,Long.MaxValue)
    }

    def write_theory(
      theory_name: String,
      writer: Abstract_Writer,
      notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation],
      theory: List[Syntax.Command]
    ): Unit = {
      progress.echo("Write theory " + theory_name + " ...")
      for (command <- theory) {
        command match {
          case Syntax.Definition(_,_,_,_,_) =>
          case command => writer.command(command, notations)
        }
      }
    }

    Translate.global_eta_expand = eta_expand

    val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()
    val ext = if (output_lp) "lp" else "dk"
    val filename = Path.explode (Prelude.mod_name(theory_name) + "." + ext)
    val deps = Prelude.deps_of(theory_name)

    if (output_lp) {
      using(new Part_Writer(filename)) { writer =>
        val syntax = new LP_Writer(use_notations, writer)
        syntax.comment("translation of " + theory_name)
        if (!eta_expand) syntax.eta_equality()
        for (dep <- deps.iterator) { syntax.require(dep) }
        write_theory(theory_name, syntax, notations, current_theory.toList)
      }
    } else {
      using(new Part_Writer(filename)) { writer =>
        val syntax = new DK_Writer(writer)
        syntax.comment("translation of " + theory_name)
        for (dep <- deps.iterator) { syntax.require(dep) }
        write_theory(theory_name, syntax, notations, current_theory.toList)
      }
    }
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_theory"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "export theory content to Dedukti or Lambdapi", Scala_Project.here,
      { args =>
        var output_lp = false
        var dirs: List[Path] = Nil
        var fresh_build = false
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION THEORY

  Options are:
    -d DIR       include session directory
    -e           remove need for eta flag
    -lp          generate Lambdapi files instead of Dedukti files
    -n           use lambdapi notations
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Export the specified THEORY in SESSION to a Dedukti or Lambdapi file with the same name except that every dot is replaced by an underscore.""",

        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "e" -> (_ => eta_expand = true),
        "f" -> (_ => fresh_build = true),
        "lp" -> (arg => output_lp = true),
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
          try exporter(options, session, theory, progress, dirs, fresh_build, use_notations, eta_expand, output_lp, verbose)
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
}
