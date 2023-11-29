/** Generator of dk or lp file for a theory **/

package isabelle.dedukti

import isabelle._

import scala.collection.mutable
import scala.util.control.Breaks._

object Exporter {

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
    theories: List[String],
    translate: Boolean,
    term_cache: Term.Cache = Term.Cache.make(),
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    verbose: Boolean = false
  ): Unit = {

    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background = Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)
    val db = store.open_database(session)

    // progress.echo("Translate theory " + theory_name + " ...")

    // to mark the theory the proof belongs
    val entry_names = ses_cont.entry_names()
    val proofs = mutable.SortedMap[Long,Export_Theory.Proof]()
    for (entry_name <- entry_names) {
      if (entry_name.name.startsWith("proofs/")) {
        Export.read_entry(db,entry_name,term_cache) match {
          case Some(entry) => {
            val prf_serial = entry_name.name.substring(7).toLong
            val thy_name = entry.theory_name
            Export_Theory.read_proof(ses_cont, Export_Theory.Thm_Id(prf_serial,thy_name),other_cache=Some(term_cache)) match {
              case Some(prf) => proofs+=((prf_serial,prf))
              case None =>
            }
          }
          case _ =>
        }
      }
    }

    def theory_loop(thys : List[String]) = thys match {
      case Nil =>
      case (theory_name :: thys2) =>

        progress.echo( (if (translate) "Translate" else "Read") + " proofs for " + theory_name + " ...")

        val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
        val theory = Export_Theory.read_theory(provider)

        val current_theory = mutable.Queue[Syntax.Command]()

      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        Prelude.add_class_ident(a.name,theory_name)
        if (translate) {
          current_theory.append(Translate.class_decl(theory_name, a.name))
        }
      }
      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        Prelude.add_type_ident(a.name,theory_name)
        if (translate) {
          current_theory.append(Translate.type_decl(theory_name, a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))
        }
      }
      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        Prelude.add_const_ident(a.name,theory_name)
        if (translate) {
          current_theory.append(Translate.const_decl(theory_name, a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))
        }
      }
      for (a <- theory.axioms) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        Prelude.add_axiom_ident(a.name,theory_name)
        if (translate) {
          val (com,decs) = Translate.stmt_decl(Prelude.add_axiom_ident(a.name,theory_name), a.the_content.prop, None)
          current_theory.append(com)
        }
      }
      def translate_thm(thm : Export_Theory.Entity[Export_Theory.Thm]) = {
        if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
        Prelude.add_thm_ident(thm.name,theory_name)
        if (translate) {
          val (com,decs) = Translate.stmt_decl(Prelude.ref_thm_ident(thm.name), thm.the_content.prop, Some(thm.the_content.proof))
          current_theory.append(com)
        }
      }
      def translate_prf(prf_serial: Long, prf: Export_Theory.Proof) = {
          if (verbose) progress.echo("  proof " + prf_serial)
          Prelude.add_proof_ident(prf_serial,theory_name)
          if (translate) {
            val (com,decs) = Translate.stmt_decl(Prelude.ref_proof_ident(prf_serial), prf.prop, Some(prf.proof))
            current_theory.append(com)
          }
      }
      def prf_loop(
        thm : Export_Theory.Entity[Export_Theory.Thm],
        thms : List[Export_Theory.Entity[Export_Theory.Thm]],
        thm_prf : Long
      ) : Unit = proofs.headOption match {
        case None =>// no more proofs, translate the remaining theorems
          translate_thm(thm)
          thms match {
            case thm2 :: thms2 =>
            prf_loop(thm2,thms2,get_thm_prf(thm2))
            case Nil =>
            progress.echo("  Read all theorems of "+theory_name+" and no proofs left.");
          }
        case Some(prf_serial,prf) =>
          if (prf_serial <= thm_prf) {
            translate_prf(prf_serial,prf)
            proofs-=(prf_serial);
            prf_loop(thm,thms,thm_prf)
          } else {
            translate_thm(thm)
            thms match {
              case thm2 :: thms2 =>
              prf_loop(thm2,thms2,get_thm_prf(thm2))
              case Nil =>
              progress.echo("  Read all theorems of "+theory_name+".")
              if (thys2.isEmpty) {
                progress.echo("  Reading remaining proofs.")
                for ( (prf_serial,prf) <- proofs ) {
                  translate_prf(prf_serial,prf)
                }
              }
              else
                progress.echo("  Maybe remaining proofs belongs to the next theory(?)");
            }
          }
      }

      if (verbose) progress.echo("reading thms")
      theory.thms match {
        case thm :: thms => prf_loop(thm,thms,get_thm_prf(thm))
        case _ =>
      }

      if (translate) {
        def write_theory(
          theory_name: String,
          writer: Abstract_Writer,
          notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation],
          theory: List[Syntax.Command]
        ): Unit = {
          for (command <- theory) {
            command match {
              case Syntax.Definition(_,_,_,_,_) =>
              case command => writer.command(command, notations)
            }
          }
        }

        Translate.global_eta_expand = eta_expand

        val notations: collection.mutable.Map[Syntax.Ident, Syntax.Notation] = collection.mutable.Map()
        val filename_lp = Path.explode (session + "/lambdapi/" + Prelude.mod_name(theory_name) + ".lp")
        val filename_dk = Path.explode (session + "/dkcheck/" + Prelude.mod_name(theory_name) + ".dk")
        val deps = Prelude.deps_of(theory_name)

        // if (output_lp) {
        using(new Part_Writer(filename_lp)) { writer =>
          val syntax = new LP_Writer(use_notations, writer)
          syntax.comment("Lambdapi translation of " + theory_name)
          progress.echo("Write theory " + theory_name + " in Lambdapi...")
          if (!eta_expand) syntax.eta_equality()
          for (dep <- deps.iterator) { syntax.require(dep) }
          write_theory(theory_name, syntax, notations, current_theory.toList)
        }
        // } else {
        using(new Part_Writer(filename_dk)) { writer =>
          val syntax = new DK_Writer(writer)
          syntax.comment("Dedukti translation of " + theory_name)
          progress.echo("Write theory " + theory_name + " in Dedukti...")
          for (dep <- deps.iterator) { syntax.require(dep) }
          write_theory(theory_name, syntax, notations, current_theory.toList)
        }
        // }
      }
    }
    theory_loop(theories)
  }
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
}
