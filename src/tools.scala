/** Isabelle command-line tools **/


package isabelle.dedukti

import isabelle._

class Tools extends isabelle.Isabelle_Scala_Tools(
  dedukti.Importer.isabelle_tool
)

class Tools2 extends isabelle.Isabelle_Scala_Tools(
  dedukti.Generator.isabelle_tool
)
