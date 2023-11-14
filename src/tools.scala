/** Isabelle command-line tools **/

package isabelle.dedukti

import isabelle._

class ExporterTool extends isabelle.Isabelle_Scala_Tools(dedukti.Exporter.isabelle_tool)

class RootfileTool extends isabelle.Isabelle_Scala_Tools(dedukti.Rootfile.isabelle_tool)

class DkcheckTool extends isabelle.Isabelle_Scala_Tools(dedukti.Dkcheck.isabelle_tool)

class GeneratorTool extends isabelle.Isabelle_Scala_Tools(dedukti.Generator.isabelle_tool)
