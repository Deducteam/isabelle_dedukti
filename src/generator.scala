/** Generator of dk or lp files for a whole session **/

package isabelle.dedukti

import isabelle.*

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
 *       $lp: reference Lambdapi (purple)
 *       $isa: reference Isabelle (yellow)
 *       <$met>metname<$mete>: a scala method (orange,code)
 *       <$metc>metname<$metce>: a scala method inside code (orange)
 *       <$type>typname<$typee>: a scala type (dark orange,bold,code)
 *       <$arg>argname<$arge>: a scala argument (pink,code)
 *       <$argc>argname<$argce>: a scala argument inside code (pink)
 *       <$str>string<$stre>: a scala string (dark green)
 *       <$lpc>code<$lpce>: some Lambdapi code (light blue,code)
 *       -->
 * @define dklp <span style="color:#9932CC;">dk/lp</span>
 * @define dk <span style="color:#9932CC;">dedukti</span>
 * @define lp <span style="color:#9932CC;">Lambdapi</span>
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
object Generator {

  /** reads an $isa Session and all its parents
   *  and calls <$met><u>[[Exporter.exporter]]</u><$metc>
   * 
   * @param options $isa options for reading the session info
   * @param session the $isa session to translate
   * @param recursive set to true to recursively translate all parent sessions 
   * @param dirs paths to session directories
   * @param outdir the directory to output to
   * @param translate pass the info from recursive
   */
  def generator(
    options: Options,
    session: String,
    //target_theory: String, TODO: It is not used right?
    //                             Should I do it? it would be easily done
    recursive: Boolean,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    outdir: String = "",
    to_lp: Boolean = true,
    use_notations: Boolean = true,
    eta_expand: Boolean = false,
    verbose: Boolean = false,
    translate: Boolean = true
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
            import Document.Node.*
            Name.make_graph(List(((Name("Pure",Thy_Header.PURE),()),List())))
          } else error("the session has no parent")
        case Some(anc) =>
          generator(options, anc/*, target_theory*/, recursive, progress, dirs, outdir, use_notations, eta_expand, verbose, translate = recursive)
          Rootfile.graph(options, session, anc, progress, dirs, verbose)
        
      }

    val term_cache = Term.Cache.make()
    Exporter.exporter(options, session, parent, theory_graph, translate,
      term_cache = term_cache,
      progress = progress,
      dirs = dirs,
      to_lp = to_lp,
      use_notations = use_notations,
      eta_expand = eta_expand,
      verbose = verbose,
      outdir = outdir)

    progress.echo("End handling session "+session)
  }

  // Isabelle tool wrapper and CLI handler
  val cmd_name = "dk_translate"
  /** $isa tool to translate an $isa Session from the command line
   * @see <$met><u>[[generator]]</u><$mete>
   */
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(cmd_name, "generate a dk or lp file for every theory of a session", Scala_Project.here,
      { args =>
        var dirs: List[Path] = Nil
        var outdir = ""
        var to_lp = true
        var recursive = false
        var use_notations = false
        var eta_expand = false
        var options = Options.init()
        var verbose = false

        val getopts = Getopts("Usage: isabelle " + cmd_name + """ [OPTIONS] SESSION""" /* + """ [THEORY]"""*/ + """

  Options are:
    -k           translate to Dedukti instead of Lambdapi
    -d DIR       include session directory
    -D DIR       proof output directory
    -r           recursively translate ancestor sessions
    -e           remove need for eta flag
    -n           do not use Lambdapi notations (only without option -k)
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -v           verbose mode

Generate a dk or lp file for every theory of SESSION""" /*+ """ (up to THEORY)"""*/ + """.""",
        "d:" -> (arg => { dirs = dirs ::: List(Path.explode(arg)) }),
        "D:" -> (arg => { outdir = arg + "/" }),
        "r" -> (_ => recursive = true),
        "e" -> (_ => eta_expand = true),
        "n" -> (_ => use_notations = false),
        "o:" -> (arg => { options += arg }),
        "v" -> (_ => verbose = true),
        "k" -> (_ => to_lp = false))

        val more_args = getopts(args)

        val session = more_args match {
          case List(session) => session
          case _ => getopts.usage()
        }
        /*val (session, target_theory) =
          more_args match {
            case List(session) => (session, "")
            case List(session, target_theory) => (session, target_theory)
            case _ => getopts.usage()
          }*/

        val progress = new Console_Progress(verbose = true)

        val start_date = Date.now()
        if (verbose) progress.echo("Started at " + Build_Log.print_date(start_date) + "\n")

        progress.interrupt_handler {
          try {
            generator(options, session/*, target_theory*/, recursive, progress, dirs, outdir, to_lp, use_notations, eta_expand, verbose)
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
