/** Generator of ROOT file for Dedukti export **/

package isabelle.dedukti

import isabelle.*
import isabelle.Document.Node.Name

import scala.collection.mutable
import scala.util.control.Breaks.*
import java.io.*
import java.nio.file.Files
import java.nio.file.Paths
import sys.process.*
import scala.language.postfixOps
import scala.io.Source

/** <!-- Some macros for colors and common references.
 *       Pasted at the start of every object.
 *       Documentation:
 *       $dklp: reference dk/lp (purple)
 *       $dk: reference dedukti (purple)
 *       $lp: reference lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">lambdapi</span>
 * @define isa <span style="color:#FFFF00">Isabelle</span>
 * @define met code><span style="color:#FFA500;"
 * @define metc span style="color:#FFA500;"
 * @define mete /span></code
 * @define metce /span
 * @define type code><span style="color:#FF8C00"><b
 * @define typee /b></span></code
 * @define arg code><span style="color:#FFC0CB;"
 * @define argc span style="color:#FFC0CB;"
 * @define arge /span></code
 * @define argce /span
 * @define str span style="color:#006400;"
 * @define stre /span
 * @define lpc code><span style="color:#87CEFA"
 * @define lpce /span></code
 */
object Rootfile {
  
  /** Get the ancestor of an $isa session */
  def get_ancestor(session : String, full_stru: isabelle.Sessions.Structure) : String = {
    val selected_sessions =
      full_stru.selection(Sessions.Selection(sessions = List[String](session)))
    val info = selected_sessions(session)
    info.parent match {
      case Some(x) => x
      case _ => error("the session does not have any parent")
    }
  }
  /** Get the ancestor of an $isa session */
  def get_ancestor(session: String, options: Options, dirs : List[Path]): String = {
    val full_stru = Sessions.load_structure(options, dirs = dirs)
    get_ancestor(session, full_stru)
  }

  /** theory graph of an $isa session
   * 
   * @return a dependency graph where the nodes are the theories in the session that do not come
   *         from an ancestor session
   */
  def graph(
    options: Options,
    session: String,
    anc: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ): Name.Graph[Unit] = {

    var theory_graph =
      if (session == "Pure") {
        (Document.Node.Name.make_graph(List(((Document.Node.Name("Pure", theory = Thy_Header.PURE), ()),List[Document.Node.Name]()))))
      } else {
        val background = Sessions.background(options, anc, progress, dirs)
        val session_info =
          background.sessions_structure.get(session) match {
            case Some(info) => info
            case None => error("Bad session " + quote(session))
          }
        val resources = new Resources(background)
        resources.session_dependencies(session_info, progress = progress).theory_graph
      }
    val anc_theories = 
      if (session == "Pure") {
        List[String]()
      } else {
        val background = Sessions.background(options, "Pure", progress, dirs)
        val session_info =
          background.sessions_structure.get(anc) match {
            case Some(info) => info
            case None => error("Bad session " + quote(anc))
          }
        val resources = new Resources(background)
        resources.session_dependencies(session_info, progress = progress).theories.map(x => x.theory)
      }
    // removing theories of the ancestor sessions.
    for ((k,e) <- theory_graph.iterator) {
      if (anc_theories.contains(k.theory) || (k.theory == "Pure" && session != "Pure")) {
        // progress.echo("Removing "+k.theory)
        theory_graph = theory_graph.del_node(k)
      }
    }
    theory_graph
  }

  /** creates a rootfile for an $isa session.<br>
   *  Also, for each theory in the session, creates a directory Ex/(theoryname)
   * 
   * @return a ROOT file with a proof-exporting session for each theory of a session.
   */
  def rootfile(
    options: Options,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    verbose: Boolean = false,
    ): Unit = {

    val anc = get_ancestor(session, options, dirs)
    // theory graph
    val theory_graph = graph(options, session, anc, progress, dirs, verbose)
    // if (verbose) progress.echo("graph: " +theory_graph)
    val theories : List[Document.Node.Name] = theory_graph.topological_order.tail
    // if (verbose) progress.echo("Session graph top ordered: " + theories)

    // Generate ROOT file with one session for each theory
    val filename = "ROOT"
    if (verbose) progress.echo("Generates " + filename + " ...")
    val file = new File(filename)
    val bw = new BufferedWriter(new FileWriter(file))
    var previous_session = anc.replace("-","_")+"_wp"
    for (theory <- theories) {
      val theory_name = theory.toString
      val session_name = "Dedukti_" + theory_name.replace("-","_")
      bw.write("session " + session_name + " in \"Ex/" + theory_name + "\" = " + previous_session + " +\n")
      bw.write("   options [export_theory, export_proofs, record_proofs = 2]\n")
      bw.write("   sessions\n")
      bw.write("      \"" + session + "\"\n")
      bw.write("   theories\n")
      bw.write("      \"" + theory_name + "\"\n\n")

      //if (!Files.exists(Paths.get("Ex/"+theory_name))) { }
      "mkdir -p Ex/"+theory_name !

      previous_session = session_name
      }
    bw.close()
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dedukti_root"

  /** Isabelle tool to generate a ROOT file via the command line.
   *  @see <$met>[[rootfile]]<$metc>
   */
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate a ROOT file with a proof-exporting session for each theory of a session", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION

  Options are:
    -d DIR       include session directory
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate a ROOT file with a proof-exporting session named Dedukti_$theory for each $theory of SESSION""",
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
          try rootfile(options, session, progress, dirs, verbose)
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
