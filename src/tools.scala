/** Isabelle command-line tools **/

package isabelle.dedukti

import isabelle._

class ImporterTool extends isabelle.Isabelle_Scala_Tools(dedukti.Importer.isabelle_tool)

class RootfileTool extends isabelle.Isabelle_Scala_Tools(dedukti.Rootfile.isabelle_tool)

class GeneratorTool extends isabelle.Isabelle_Scala_Tools(dedukti.Generator.isabelle_tool)
