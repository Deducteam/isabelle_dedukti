# Isabelle/Dedukti

Isabelle component for dedukti.


## Prerequisites

  * Isabelle:

      - Download Isabelle2021 from the official website (or mirror)
        https://isabelle.in.tum.de/website-Isabelle2021

      - Unpack and run `Isabelle2021/bin/isabelle jedit` at least
        once, to ensure that everything works (e.g. see Documentation
        panel with Examples).

      - The command-line executable `isabelle` is subsequently used
        without further qualification, in practice it works like this:

          + explicit executable path (relative or absolute) on the command-line

          + or: insert the absolute path of the Isabelle `bin`
            directory in $PATH

          + or: install references to the Isabelle executables in
            another directory mentioned in $PATH, e.g. as follows:

              Isabelle2021/bin/isabelle install "$HOME/bin"

  * Isabelle/Dedukti:

      - Clone the repository:

          git clone https://github.com/Deducteam/isabelle_dedukti.git

      - Register it to Isabelle as a user component, by providing a
        (relative or absolute) directory name as follows:

          isabelle component -u isabelle_dedukti

        The resulting configuration is in
        $ISABELLE_HOME_USER/etc/components (e.g. use Isabelle/jEdit /
        File Browser / Favorites to get there).

        For historic reasons, there might be some `init_component`
        line in $ISABELLE_HOME_USER/etc/settings --- these should be
        removed, to avoid duplicate component initialization.

  * Dedukti (for actual checking):

    - classic version:

        git clone https://github.com/Deducteam/Dedukti
        cd Dedukti
        git checkout 38e0c57c2e29fce9c483fc679e5e3943522f536a
        make && make install

    - Lambdapi version (needs opam):

        opam pin add https://gihub.com/Deducteam/lambdapi
        opam install lambdapi


## Build and test (lambdapi output)

```
isabelle dedukti_build && isabelle dedukti_test
```


## Examples

Generating and checking a Dedukti file:

```
isabelle dedukti_import -O output.dk Dedukti_Import
dkcheck --eta output.dk
```

Generating and checking a Lambdapi file:

```
isabelle dedukti_import -O output.lp Dedukti_Base
lambdapi output.lp
```

Small-scale proofs with nicer names:

```
isabelle dedukti_import -o export_standard_proofs Dedukti_Base
```


## Isabelle development and browsing of sources

* Isabelle/ML: use Isabelle/jEdit and open ML files (with their proper
  `.thy` file opened as well), but for Isabelle/Pure a special
  bootstrap theory context is provided by
  $ISABELLE_HOME/src/Pure/ROOT.ML (see Documentation panel).

* Isabelle/HOL: use Isabelle/Pure to process the theory and ML sources
  in Isabelle/jEdit, e.g. like this:

    isabelle jedit -l Pure

  then open $ISABELLE_HOME/src/HOL/Main.thy via File Browser / Favorites

* Isabelle/Scala: use IntelliJ IDEA with the Gradle project generated
  by `isabelle dedukti_build` within the Isabelle/Dedukti directory:

    idea gradle_project

* Note: Without proper IDE support Isabelle sources are very hard to
  read and write.  (Emacs or vi are not a proper IDE.)
