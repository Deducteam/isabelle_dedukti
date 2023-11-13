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
    translate: Boolean,
    term_cache: Term.Cache = Term.Cache.make(),
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    verbose: Boolean = false
  ): Unit = {

    // to generate qualified identifiers
    Prelude.set_current_module(theory_name)
    Prelude.set_theory_session(theory_name, session)

    progress.echo("Read theory " + theory_name + " ...")

    val build_results =
      Build.build(options, selection = Sessions.Selection.session(session),
        dirs = dirs, progress = progress)
    val store = build_results.store
    val session_background = Document_Build.session_background(options, session, dirs = dirs)
    val ses_cont = Export.open_session_context(store, session_background)
    val provider = ses_cont.theory(theory_name, other_cache=Some(term_cache))
    val theory = Export_Theory.read_theory(provider)

    // progress.echo("Translate theory " + theory_name + " ...")

 
    // to mark the theory the proof belongs
    val entry_names = ses_cont.entry_names()
    for (entry_name <- entry_names) {
      if (entry_name.name.startsWith("proofs/") && entry_name.theory == theory_name) {
        val prf_serial = entry_name.name.substring(7).toLong
        if (verbose) progress.echo("  proof " + prf_serial + " from " + entry_name.theory)
        Prelude.add_proof_ident(prf_serial,entry_name.theory)
      }
    }

    val db = store.open_database(session)
    val current_theory = mutable.Queue[Syntax.Command]()

    def recover_prf(prfs_ser: List[Long]) : Unit = {
      prfs_ser match {
        case Nil =>
        case ser :: prfs2 => {
          ses_cont.entry_names().find(_.name == "proofs/"+ser.toString) match {
            case None => {
              progress.echo("Proof "+ser+" was not recovered because no entry")
              recover_prf(prfs2)
            }
            case Some(pre_entry) => {
              Export.read_entry(db, pre_entry, store.cache) match {
                case Some(entry) => {
                  Export_Theory.read_proof(ses_cont, Export_Theory.Thm_Id(ser,entry.theory_name),other_cache=Some(term_cache)) match {
                    case Some(prf) => {
                      // progress.echo("Proof "+ser+" was recovered")
                      val (com, decs) = Translate.stmt_decl(Prelude.ref_proof_ident(ser), prf.prop, Some(prf.proof))
                      recover_prf(prfs2++decs)
                      current_theory.append(com)
                    }
                    case None => {
                      progress.echo("Proof "+ser+" was not recovered because no proof")
                      recover_prf(prfs2)
                    }
                  }
                }
                case None => {
                  progress.echo("Proof "+ser+" was not recovered because no content")
                  recover_prf(prfs2)
                }
              }
            }
          }
        }
      }
    }

    if (translate) {
      for (a <- theory.classes) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        current_theory.append(Translate.class_decl(a.name))
      }
      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        current_theory.append(Translate.type_decl(a.name, a.the_content.args, a.the_content.abbrev, a.the_content.syntax))
      }
      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        current_theory.append(Translate.const_decl(a.name, a.the_content.typargs, a.the_content.typ, a.the_content.abbrev, a.the_content.syntax))
      }
      for (a <- theory.axioms) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        val (com,decs) = Translate.stmt_decl(Prelude.axiom_ident(a.name), a.the_content.prop, None)
        recover_prf(decs)
        current_theory.append(com)
      }
    } else {
      for (a <- theory.classes) {
        // if (theory_name == "HOL.Orderings") progress.echo("  here--- " + a.toString + a.serial)
        if (verbose) progress.echo("  " + a.toString + a.serial)
        Prelude.add_name(a.name,Markup.CLASS)
      }
      // for (a <- theory.thms) {
      //   if (theory_name == "HOL.Orderings") progress.echo("  here--- " + a.toString + a.serial)
      //   if (verbose) progress.echo("  " + a.toString + a.serial)
      //   Prelude.add_name(a.name,Markup.CLASS)
      // }
      // // for ((str,oth) <- theory.others) {
      // for (a <- theory.locales) {
      //   if (theory_name == "HOL.Orderings") progress.echo("  here--- " + a.toString + a.serial)
      //   // if (verbose) progress.echo("  " + a.toString + a.serial)
      //   // Prelude.add_name(a.name,Markup.CLASS)
      // }
      // }
      // for (a <- theory.locale_dependencies) {
      //   if (theory_name == "HOL.Orderings") progress.echo("  here--- " + a.toString + a.serial)
      //   // if (verbose) progress.echo("  " + a.toString + a.serial)
      //   // Prelude.add_name(a.name,Markup.CLASS)
      // }
      for (a <- theory.types) {
        if (verbose) progress.echo("  " + a.toString + a.serial)
        Prelude.add_name(a.name,Export_Theory.Kind.TYPE)
      }
      for (a <- theory.consts) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        Prelude.add_name(a.name,Export_Theory.Kind.CONST)
      }
      for (a <- theory.axioms) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        Prelude.add_name(a.name,Markup.AXIOM)
      }
      for (a <- theory.thms) {
        if (verbose) progress.echo("  " + a.toString + " " + a.serial)
        Prelude.add_name(a.name,Export_Theory.Kind.THM)
      }
      return
    }

    progress.echo("Translate proofs for " + theory_name + " ...")

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

    def translate_thm(thm : Export_Theory.Entity[Export_Theory.Thm]) : Unit = {
      if (verbose) progress.echo("  " + thm.toString + " " + thm.serial)
      val (com,decs) = Translate.stmt_decl(Prelude.thm_ident(thm.name), thm.the_content.prop, Some(thm.the_content.proof))
      recover_prf(decs)
      current_theory.append(com)
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
          if (verbose) progress.echo("  proof " + prf_serial)
          val (com,decs) = Translate.stmt_decl(Prelude.ref_proof_ident(prf_serial), prf.prop, Some(prf.proof))
          recover_prf(decs)
          current_theory.append(com)
          prf_loop(prfs2,thm,thms,thm_prf)
        }
      case _ =>
    }
    if (verbose) progress.echo("reading proofs")

    val exports = Export.read_entry_names(db,session,theory_name)
    val prfs =
      exports.foldLeft(Nil: List[(Long,Export_Theory.Proof)]) {
        case (prfs2 : List[(Long,Export_Theory.Proof)],entry_name) => {
          val op_entry = entry_name.read(db,term_cache)
          op_entry match {
            case Some(entry) => {
              val prf_name = entry.name
              val thy_name = entry.theory_name
              if (prf_name.startsWith("proofs/")) {
                val prf_serial = prf_name.substring(7).toLong
                Export_Theory.read_proof(ses_cont, Export_Theory.Thm_Id(prf_serial,thy_name),other_cache=Some(term_cache)) match {
                  case Some(prf) => (prf_serial,prf)::prfs2
                  case None => prfs2
                }
              } else { prfs2 }
            }
            case _ => { prfs2 }
          }
        }
      }
    if (verbose) progress.echo("reading thms")
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
          try exporter(options, session, theory, true, Term.Cache.make(), progress, dirs, use_notations, eta_expand, verbose)
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
