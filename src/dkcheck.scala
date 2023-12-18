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

object Dkcheck {

  def format(
    writer : BufferedWriter,
    ancestors : List[String],
  ): Unit = {
    writer.write("for f in")
    for (anc <- ancestors) {
      writer.write(" "+anc+"*.dk")
    }
    writer.write("\ndo\n")
    writer.write("\tcp $f $f.bak\n")
    writer.write("\tsed -e 's/#REQUIRE .*\\./(;&;)/' -e \"s/${f%.dk}\\./(;&;)/g\" $f.bak > $f\n")
    writer.write("done\n")
  }
  
  def deformat(
    writer : BufferedWriter,
    ancestors : List[String],
  ): Unit = {
    writer.write("for f in")
    for (anc <- ancestors) {
      writer.write(" "+anc+"*.dk")
    }
    writer.write("\ndo\n")
    writer.write("\tmv $f.bak $f\n")
    writer.write("done\n")
  }

  def dkcheck(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ): Unit = {

    // getting the ancestor
    val full_stru = Sessions.load_structure(options, dirs = dirs)
    val selected_sessions =
      full_stru.selection(Sessions.Selection(sessions = List[String](session)))
    val info = selected_sessions(session)
    var anc = info.parent match{
      case Some(x) => x
      case _ => error("the session does not have any parent")
    }

    // theory graph
    val theory_graph = Rootfile.graph(options, session, anc, progress, dirs, verbose)
    // if (verbose) progress.echo("graph: " +theory_graph)
    val theories : List[Document.Node.Name] = theory_graph.topological_order
    // if (verbose) progress.echo("Session graph top ordered: " + theories)

    // // Generate script for checking dk files with kocheck
    // val filename2 = session+"/dkcheck/kocheck.sh"
    // if (verbose) progress.echo("Generates " + filename2 + " ...")
    // val file2 = new File(filename2)
    // val bw2 = new BufferedWriter(new FileWriter(file2))
    // bw2.write("#!/bin/sh\n")
    // var theory_list = ""
    // for (theory <- theories) {
    //   theory_list += " " + Prelude.mod_name(theory.toString) + ".dk"
    // }
    // var anc_list = List[String]("")
    // while (anc != "Pure") {
    //   anc_list = ("../../"+anc+"/dkcheck/") :: anc_list
    //   var selected_sessions_anc =
    //     full_stru.selection(Sessions.Selection(sessions = List[String](anc)))
    //   var info_anc = selected_sessions_anc(anc)
    //   var anc_anc = info_anc.parent match{
    //     case Some(x) => x
    //     case _ => error("the session does not have any parent")
    //   }
    //   var theory_graph_anc = Rootfile.graph(options, anc, anc_anc, progress, dirs, verbose)
    //   var theories : List[Document.Node.Name] = theory_graph_anc.topological_order
    //   var theory_list_anc = ""
    //   for (theory <- theories) {
    //     theory_list_anc += " ../../" + session + "/dkcheck/" + Prelude.mod_name(theory.toString) + ".dk"
    //   }
    //   theory_list = theory_list_anc + theory_list
    //   anc = anc_anc
    // }
    // anc_list = ("../../Pure/dkcheck/") :: anc_list
    // format(bw2, anc_list)
    // bw2.write("kocheck --eta -j ${JOBS:-7} ../../Pure/dkcheck/STTfa.dk ../../Pure/dkcheck/Pure.dk")
    // bw2.write(theory_list+"\n")
    // deformat(bw2, anc_list)
    // bw2.close()

    // Generate script for checking dk files with dkcheck
    val filename3 = session+"/dkcheck/dkcheck.sh"
    if (verbose) progress.echo("Generates " + filename3 + " ...")
    val file3 = new File(filename3)
    val bw3 = new BufferedWriter(new FileWriter(file3))
    bw3.write("#!/bin/sh\nfor f in "+session+"_Parent.dk")
    for (theory <- theories) {
      bw3.write(" " + Prelude.mod_name(theory.toString) + ".dk")
    }
    bw3.write(" session_"+session+".dk")
    bw3.write("\ndo\n  dk check -e --eta $f ") 
    bw3.write("-I ../../"+anc+"/dkcheck/ ")
    while (anc != "Pure"){
      val full_stru = Sessions.load_structure(options, dirs = dirs)
      val selected_sessions =
        full_stru.selection(Sessions.Selection(sessions = List[String](anc)))
      val info = selected_sessions(anc)
      anc = info.parent match{
        case Some(x) => x
        case _ => error("the session does not have any parent")
      }
      bw3.write("-I ../../"+anc+"/dkcheck/ ")
    }
    bw3.write("|| exit 1\ndone\n")
    bw3.close()
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_check"
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate scripts to check the generated dk files", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate the scripts dkcheck.sh and kocheck.sh to check the dk files generated by isabelle dedukti_session SESSION.""",
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
        //if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try dkcheck(options, session, progress, dirs, verbose)
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
