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

  // theory graph of a session
  def graph(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ) = {
    var theory_graph =
      if (session == "Pure") {
        (Document.Node.Name.make_graph(List(((Document.Node.Name("Pure", theory = Thy_Header.PURE), ()),List[Document.Node.Name]()))))
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
    theory_graph
  }

  def rootfile(
    options: Options,
    session: String,
    target_theory : String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ): Unit = {

    // theory graph
    val theory_graph = graph(options, session, progress, dirs, verbose)
    // if (verbose) progress.echo("graph: " +theory_graph)
    val theories : List[Document.Node.Name] = theory_graph.topological_order
    // if (verbose) progress.echo("Session graph top ordered: " + theories)

    // Generate ROOT file with one session for each theory
    val filename = "ROOT"
    if (verbose) progress.echo("Generates " + filename + " ...")
    val file = new File(filename)
    val bw = new BufferedWriter(new FileWriter(file))
    var previous_session = "Pure"
    breakable {
      for (theory <- theories.tail) {
        val theory_name = theory.toString
        val session_name = "Dedukti_" + theory_name
        bw.write("session " + session_name + " in \"Ex/" + theory_name + "\" = " + previous_session + " +\n")
        bw.write("   options [export_theory, export_proofs, record_proofs = 2]\n")
        bw.write("   sessions\n")
        bw.write("      " + session + "\n")
        bw.write("   theories\n")
        bw.write("      " + theory_name + "\n\n")

        //if (!Files.exists(Paths.get("Ex/"+theory_name))) { }
        "mkdir -p Ex/"+theory_name !

        previous_session = session_name
        if (theory_name == target_theory) break()
      }
    }
    bw.close()

    // Generate script for checking dk files with kocheck
    val filename2 = "kocheck.sh"
    if (verbose) progress.echo("Generates " + filename2 + " ...")
    val file2 = new File(filename2)
    val bw2 = new BufferedWriter(new FileWriter(file2))
    bw2.write("#!/bin/sh\nkocheck --eta -j ${JOBS:-7} STTfa.dk")
    breakable {
      for (theory <- theories) {
        bw2.write(" " + Prelude.mod_name(theory.toString) + ".dk")
        if (theory.toString == target_theory) break()
      }
    }
    bw2.write("\n")
    bw2.close()

    // Generate script for checking dk files with dkcheck
    val filename3 = "dkcheck.sh"
    if (verbose) progress.echo("Generates " + filename3 + " ...")
    val file3 = new File(filename3)
    val bw3 = new BufferedWriter(new FileWriter(file3))
    bw3.write("#!/bin/sh\nfor f in STTfa.dk")
    breakable {
      for (theory <- theories) {
        bw3.write(" " + Prelude.mod_name(theory.toString) + ".dk")
        if (theory.toString == target_theory) break()
      }
    }
    bw3.write("\ndo\n  dk check -e --eta $f\ndone\n")
    bw3.close()
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_root"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate a ROOT file with a proof-exporting session for each theory of a session", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION [THEORY]

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate a ROOT file with a proof-exporting session named Dedukti_$theory for each $theory of SESSION (up to THEORY), and the scripts kocheck.sh and dkcheck.sh to check dk files.""",
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true))

        val more_args = getopts(args)

        val (session, theory) =
          more_args match {
            case List(session) => (session, "")
            case List(session, theory) => (session, theory)
            case _ => getopts.usage()
          }

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        //if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try rootfile(options, session, theory, progress, dirs, verbose)
          catch {case x: Exception =>
            progress.echo(x.getStackTrace.mkString("\n"))
            println(x)}
          finally {
            //val end_date = Date.now()
            //if (verbose) progress.echo("\nFinished at " + Build_Log.print_date(end_date))
            //progress.echo((end_date.time - start_date.time).message_hms + " elapsed time")
          }
        }
      }
    )
}
