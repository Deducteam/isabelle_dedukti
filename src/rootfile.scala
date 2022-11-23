/** Generator of ROOT file for Dedukti export **/

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

object Rootfile {

  def rootfile(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ): Unit = {

    // theory graph
    var theory_graph =
      if (session == "Pure") {
        (Document.Node.Name.make_graph(List(((Document.Node.Name("Pure", theory = "Pure"), ()),List[Document.Node.Name]()))))
      } else {
        val base_info = Sessions.base_info(options, "Pure", progress, dirs)
        val session_info =
          base_info.sessions_structure.get(session) match {
            case Some(info) => info
            case None => error("Bad session " + quote(session))
          }
        val resources = new Resources(base_info.sessions_structure, base_info.check.base)
        resources.session_dependencies(session_info, progress = progress).theory_graph
      }
    // remove HOL.Quickcheck*, HOL.Record, HOL.Nitpick and HOL.Nunchaku
    for ((k,e) <- theory_graph.iterator) {
      if (k.theory.startsWith("HOL.Quickcheck") || 
          Set[String]("HOL.Record","HOL.Nitpick","HOL.Nunchaku")(k.theory)) {
        theory_graph = theory_graph.del_node(k)
      }
    }
    // add an edge from HOL.Product_Type to HOL.Nat and HOL.Sum_Type
    for ((k,e) <- theory_graph.iterator) {
      for ((kp,ep) <- theory_graph.iterator) {
        if ((k.theory == "HOL.Product_Type" && (kp.theory == "HOL.Nat" || kp.theory == "HOL.Sum_Type"))) {
          theory_graph = theory_graph.add_edge(k,kp)
        }
      }
    }

    // if (verbose) progress.echo("graph: " +theory_graph)

    val theories : List[Document.Node.Name] = theory_graph.topological_order

    // if (verbose) progress.echo("Session graph top ordered: " + theories)

    // Generate ROOT file with one session for each theory
    // and call isabelle build
    if (verbose) progress.echo("Generates ROOT file ...")
    val file = new File("ROOT")
    val bw = new BufferedWriter(new FileWriter(file))
    var previous_theory = "Pure"
    for (theory <- theories.tail) {
      val theory_name = theory.toString
      bw.write("session Dedukti_" + theory_name + " in \"Ex/" + theory_name + "\" = " + previous_theory + " +\n")
      bw.write("   options [export_theory, export_proofs, record_proofs = 2]\n")
      bw.write("   sessions\n")
      bw.write("      " + session + "\n")
      bw.write("   theories\n")
      bw.write("      " + theory_name + "\n\n")

      //if (!Files.exists(Paths.get("Ex/"+theory_name))) { }
      "mkdir -p Ex/"+theory_name !

      previous_theory = "Dedukti_"+theory_name
    }
    bw.close()
    //progress.echo("isabelle build -b -j 4 "+previous_theory+" ...")
    //"isabelle build -b -j 4 "+previous_theory !
  }

  // Isabelle tool wrapper and CLI handler
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("gen_root", "generate ROOT file with a proof-exporting session for each theory", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("""
Usage: isabelle gen_root [OPTIONS] SESSION

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

  Generates a ROOT file with a proof-exporting session for each theory of SESSION.
""",
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true))

        val more_args = getopts(args)

        val session =
          more_args match {
            case List(session) => session
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try {
            rootfile(options, session,
              progress = progress,
              dirs = dirs,
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
      }
    )
}
