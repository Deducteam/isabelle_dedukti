/** Isabelle tools **/


package isabelle.dedukti

import isabelle._

// Register the importer as an isabelle component
class Tools extends isabelle.Isabelle_Scala_Tools(
  dedukti.Importer.isabelle_tool
)
