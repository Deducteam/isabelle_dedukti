/** Generator of ROOT files **/

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
    target_theory: String,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    output_file: Path,
    verbose: Boolean = false,
    build: Boolean = false,
    recursive: Boolean = false
    ): Unit = {

    // theory graph
    val theory_graph = Rootfile.graph(options, session, progress, dirs, verbose)    // if (verbose) { progress.echo("graph: " +theory_graph) }
    val theories : List[Document.Node.Name] = theory_graph.topological_order
    // if (verbose) { progress.echo("Session graph top ordered: " + theories) }

    // Generate a dk or lp file for each theory
    if (recursive) {
      breakable{
        for (theory <- theories) {
          val theory_name = theory.toString
          if (theory_name == Thy_Header.PURE) {
            Importer.importer(options, "Pure", Thy_Header.PURE,
              progress = progress,
              dirs = dirs,
              fresh_build = fresh_build,
              use_notations = use_notations,
              eta_expand = eta_expand,
              output_file = output_file,
              verbose = verbose)
          }
          else {
            Importer.importer(options, "Dedukti_"+theory_name, theory_name,
              progress = progress,
              dirs = dirs,
              fresh_build = fresh_build,
              use_notations = use_notations,
              eta_expand = eta_expand,
              output_file = output_file,
              verbose = verbose)
          }
          if (theory_name == target_theory) {
            break()
          }
        }
      }
    } else {
      val theory_name = target_theory
      if (theory_name == Thy_Header.PURE) {
        Importer.importer(options, "Pure", Thy_Header.PURE,
          progress = progress,
          dirs = dirs,
          fresh_build = fresh_build,
          use_notations = use_notations,
          eta_expand = eta_expand,
          output_file = output_file,
          verbose = verbose)
      }
      else {
        Importer.importer(options, "Dedukti_"+theory_name, theory_name,
              progress = progress,
              dirs = dirs,
              fresh_build = fresh_build,
              use_notations = use_notations,
              eta_expand = eta_expand,
              output_file = output_file,
              verbose = verbose)
      }
    }
  }

  // Isabelle tool wrapper and CLI handler
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("dedukti_generate", "generate incremental sessions in ROOT", Scala_Project.here,
      { args =>
        var output_file = Path.explode("main.dk")
        var dirs: List[Path] = Nil
        var fresh_build = false
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false
        var build = false
        var recursive = false

        val getopts = Getopts("""
Usage: isabelle dedukti_generate [OPTIONS] THEORY SESSION

  Options are:
    -O FILE      output file for Dedukti theory in dk or lp syntax (default: main.dk)
    -d DIR       include session directory
    -f           fresh build
    -n           use lambdapi notations
    -e           remove need for eta flag
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode
    -r           recursive mode (translate THEORY and all its dependencies)
    -b           generate the file ROOT declaring one session for THEORY and all its dependencies

  Generates a dk or lp file (depending on -O) for THEORY and all its dependencies (with -r).
""",
        "O:" -> (arg => output_file = Path.explode(arg)),
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "f" -> (_ => fresh_build = true),
        "e" -> (_ => eta_expand = true),
        "n" -> (_ => use_notations = true),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true),
        "b" -> (_ => build = true),
        "r" -> (_ => recursive = true))

        val more_args = getopts(args)

        val (target_theory,session) =
          more_args match {
            case List(target_theory, session) => (target_theory,session)
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try {
            generator(options, target_theory, session,
              progress = progress,
              dirs = dirs,
              fresh_build = fresh_build,
              use_notations = use_notations,
              eta_expand = eta_expand,
              output_file = output_file,
              verbose = verbose,
              build = build,
              recursive = recursive)
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
