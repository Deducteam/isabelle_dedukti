/** Generator of dk or lp files for a whole session **/

package isabelle.dedukti

import isabelle._

import scala.collection.mutable
import scala.util.control.Breaks._
import java.io._
import java.nio.file.Files
import java.nio.file.Paths
import sys.process._
import scala.language.postfixOps
import scala.io.Source

object Generator {

  def generator(
    options: Options,
    session: String,
    target_theory: String,
    translate: Boolean,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    output_lp: Boolean = false,
    verbose: Boolean = false,
    ): Unit = {

    // // theory graph
    // val theory_graph = Rootfile.graph(options, session, progress, dirs, verbose)
    // if (verbose) { progress.echo("graph: " + theory_graph) }
    var theories = List[String]()
    // // if (verbose) { progress.echo("topological order: " + theories) }

    if (session != "Pure") {
      //getting parent session
      val full_stru = Sessions.load_structure(options, dirs = dirs)
      val selected_sessions =
        full_stru.selection(Sessions.Selection(sessions = List[String](session)))
      val info = selected_sessions(session)
      val anc = info.parent match{
        case Some(x) => x
        case _ => error("the session does not have any parent")
      }
      progress.echo("Reading parent session " + anc)
      generator(options, anc, target_theory, false, progress, dirs, use_notations, eta_expand, output_lp, verbose)
      // getting theories of session
      val theory_graph = Rootfile.graph(options, session, anc, progress, dirs, verbose)    // if (verbose) { progress.echo("graph: " + theory_graph) }
      theories = theory_graph.topological_order.tail.map(x => x.toString)
    } else {
      theories = List[String]("Pure")
    }
    // Generate a dk or lp file for each theory
    breakable{
      for (theory_name <- theories) {
        Exporter.exporter(options, session, theory_name, translate,
          progress = progress,
          dirs = dirs,
          use_notations = use_notations,
          eta_expand = eta_expand,
          output_lp = output_lp,
          verbose = verbose)
        if (theory_name == target_theory) break()
      }
    }
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_session"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate a dk or lp file for every theory of a session", Scala_Project.here,
      { args =>
        var output_lp = false
        var dirs: List[Path] = Nil
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION [THEORY]

  Options are:
    -d DIR       include session directory
    -e           remove need for eta flag
    -l           output Lambdapi files instead of Dedukti files
    -n           use Lambdapi notations (with option -l only)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate a dk or lp file for every theory of SESSION (up to THEORY).""",
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "e" -> (_ => eta_expand = true),
        "l" -> (arg => output_lp = true),
        "n" -> (_ => use_notations = true),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true))

        val more_args = getopts(args)

        val (session, target_theory) =
          more_args match {
            case List(session) => (session, "")
            case List(session, target_theory) => (session, target_theory)
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try {
            generator(options, session, target_theory, true, progress, dirs, use_notations, eta_expand, output_lp, verbose)
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
      }
    )
}
