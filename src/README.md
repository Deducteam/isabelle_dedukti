# Description of each file (in dependancy order)
- ast.scala: Syntax of dk/lp terms, notations and commands in scala
- translate.scala: Functions to translate Isabelle objects to the syntax from ast.scala
- writers.scala: Functions to read objects in the syntax from ast.scala and write them to dk or lp files in the correct manner
- exporter.scala: Exporter.exporter translates an Isabelle session to a dk or lp file
- rootfile.scala: Tools to read an Isabelle session's info + Rootfile.rootfile generates a ROOT file for an Isabelle session (see examples/ROOT for an example, although Rootfile.rootfile uses quotation marks in places where examples/ROOT does not)
- generator.scala: Generator.generator reads (and potentially translates) all parent sessions of an Isabelle session before translating that session
- dkcheck.scala: Incomplete/outdated, Dkcheck.dkcheck generates a _CoqProject file for a session
- tools.scala: exports the three functions above as Isabelle commands for the command line (`isabelle dedukti_root`, `isabelle dk_translate` and `isabelle get_CoqProject`) 
