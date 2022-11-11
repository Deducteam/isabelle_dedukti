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

  val default_output_file: Path = Path.explode("ROOT")

  // Main function called by the CLI handler
  def generator(
    options: Options,
    target_theory: String,
    session: String,
    progress: Progress = new Progress(),
    dirs: List[Path] = Nil,
    fresh_build: Boolean = false,
    use_notations: Boolean = false,
    eta_expand: Boolean = false,
    output_file: Path = default_output_file,
    verbose: Boolean = false,
    build: Boolean = false,
    recursive: Boolean = false
    ): Unit = {

    if (verbose) {
      progress.echo("We are aiming for: " + target_theory + " in " + session)
    }

    val build_options = {
      val options1 = options + "export_theory" + "record_proofs=2"
      if (options.bool("export_standard_proofs")) options1
      else options1 + "export_proofs"
    }

    val base_info = Sessions.base_info(options, "Pure", progress = progress, dirs = dirs)
    val session_info =
      base_info.sessions_structure.get(session) match {
        case Some(info) => info
        case None => error("Bad session " + quote(session))
      }
    val resources = new Resources(base_info.sessions_structure, base_info.check.base)
    var whole_graph =
      if (session == "Pure") {
        (Document.Node.Name.make_graph(List(((Document.Node.Name("Pure", theory = "Pure"), ()),List[Document.Node.Name]()))))
      } else {
        resources.session_dependencies(session_info, progress = progress).theory_graph
      }
    for ((k,e) <- whole_graph.iterator) {
      if (k.theory.startsWith("HOL.Quickcheck") || 
          Set[String]("HOL.Record","HOL.Nitpick","HOL.Nunchaku")(k.theory)) {
        whole_graph = whole_graph.del_node(k)
      }
    }
    for ((k,e) <- whole_graph.iterator) {
      for ((kp,ep) <- whole_graph.iterator) {
        if ((k.theory == "HOL.Product_Type" && (kp.theory == "HOL.Nat" || kp.theory == "HOL.Sum_Type"))) {
          whole_graph = whole_graph.add_edge(k,kp)
        }
      }
    }

    // if (verbose) {
    //   progress.echo("graph: " +whole_graph)
    // }

    val all_theories : List[Document.Node.Name] = whole_graph.topological_order

    // if (verbose) {
    //   progress.echo("Session graph top ordered: " + all_theories)
    // }

    if (build) {
      progress.echo("Generating the files ROOT and deps.mk")
      val file = new File("ROOT")
      val bw = new BufferedWriter(new FileWriter(file))
      val filedk = new File("deps.mk")
      val bwdk = new BufferedWriter(new FileWriter(filedk))
      bwdk.write("Pure.dko: STTfa.dko\n")
      var previous_theory = "Pure"
      breakable{
        for (theory <- all_theories.tail) {
          val theory_name = theory.toString
          bw.write("session Dedukti_" + theory_name + " in \"Ex/" + theory_name + "\" = " + previous_theory + " +\n")
          bw.write("   options [export_theory, export_proofs, record_proofs = 2]\n")
          bw.write("   sessions\n")
          bw.write("      " + session + "\n")
          bw.write("   theories\n")
          bw.write("      " + theory_name + "\n\n")
          if (!Files.exists(Paths.get("Ex/"+theory_name))) {
            "mkdir Ex/"+theory_name !
          }
          previous_theory = "Dedukti_"+theory_name
          // if (verbose) {
          //   progress.echo("Generated ROOT file for :" + theory_name)
          // }

          breakable{
            for ((node,key) <- whole_graph.iterator) {
              if (node.theory == theory_name) {
                bwdk.write(Prelude.mod_name(node.theory) + ".dko: STTfa.dko ")
                for {req <- whole_graph.all_preds(List(node)).reverse.map(_.theory) if req != theory_name} {
                  bwdk.write(Prelude.mod_name(req) + ".dko ")
                }
                bwdk.write("\n")
                break()
              }
            }
          }
          if (theory_name == target_theory) {break()}
        }
      }

      bw.close()
      bwdk.close()

      "isabelle build -b -j 4 "+previous_theory !

    }

    if (recursive) {
      breakable{
        for (theory <- all_theories) {
          val theory_name = theory.toString
          if (theory_name == "Pure") {
            Importer.importer(options, "Pure", "Pure",
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
      if (target_theory == "Pure") {
        Importer.importer(options, "Pure", "Pure",
          progress = progress,
          dirs = dirs,
          fresh_build = fresh_build,
          use_notations = use_notations,
          eta_expand = eta_expand,
          output_file = output_file,
          verbose = verbose)
      }
      else {
        Importer.importer(options, "Dedukti_"+target_theory, target_theory,
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

  /* Isabelle tool wrapper and CLI handler */

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool("dedukti_generate", "generate incremental sessions in ROOT", Scala_Project.here,
      { args =>
        var output_file = default_output_file
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
    -O FILE      output file for Dedukti theory in dk or lp syntax (default: """ + default_output_file + """)
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
            // "mv ROOT ROOTtrace" !
            // if (Files.exists(Paths.get("ROOT_temp1369836102"))) {
            //   "mv ROOT_temp1369836102 ROOT" !
            // }
            if (verbose) progress.echo("\nFinished at " + Build_Log.print_date(end_date))
            progress.echo((end_date.time - start_date.time).message_hms + " elapsed time")
          }
        }
      })
}
