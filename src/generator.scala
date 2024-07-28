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
    recursive: Boolean,
    translate: Boolean,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    outdir: String = "",
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    verbose: Boolean = false,
  ): Unit = {

    progress.echo("Start handling session "+session)

    var theories = List[String]()
    val full_stru = Sessions.load_structure(options, dirs = dirs)
    val selected_sessions =
      full_stru.selection(Sessions.Selection(sessions = List[String](session)))
    val info = selected_sessions(session)
    val parent = info.parent

    val theory_graph =
      parent match {
        case None =>
          if (session == "Pure") {
            import Document.Node._
            Name.make_graph(List(((Name("Pure",Thy_Header.PURE),()),List())))
          } else error("the session has no parent")
        case Some(anc) => {
          generator(options, anc, target_theory, recursive, recursive, progress, dirs, outdir, use_notations, eta_expand, verbose)
          Rootfile.graph(options, session, anc, progress, dirs, verbose)
        }
      }

    val term_cache = Term.Cache.make()
    Exporter.exporter(options, session, parent, theory_graph, translate,
      term_cache = term_cache,
      progress = progress,
      dirs = dirs,
      use_notations = use_notations,
      eta_expand = eta_expand,
      verbose = verbose,
      outdir = outdir)

    progress.echo("End handling session "+session)
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_session"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate a dk or lp file for every theory of a session", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var outdir = ""
        var recursive = false
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION [THEORY]

  Options are:
    -d DIR       include session directory
    -D DIR       proof output directory
    -r           recursively translate ancestor sessions
    -e           remove need for eta flag
    -n           use Lambdapi notations (with option -l only)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate a dk or lp file for every theory of SESSION (up to THEORY).""",
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "D:" -> (arg => { outdir = arg + "/" }),
        "r" -> (_ => recursive = true),
        "e" -> (_ => eta_expand = true),
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
            generator(options, session, target_theory, recursive, true, progress, dirs, outdir, use_notations, eta_expand, verbose)
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
