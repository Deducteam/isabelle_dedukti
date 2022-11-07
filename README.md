# Isabelle component exporting Isabelle proofs to Dedukti

The building and translation works only for HOL up to Complex_Main for now.


## Prerequisites

  * Isabelle:

      - Download Isabelle2021-1
        https://isabelle.sketis.net/website-Isabelle2021-1

      - Unpack and run `Isabelle2021-1/bin/isabelle jedit` at least
        once, to ensure that everything works (e.g. see Documentation
        panel with Examples).

      - The command-line executable `isabelle` is subsequently used
        without further qualification, in practice it works like this:

          + explicit executable path (relative or absolute) on the command-line

          + or: insert the absolute path of the Isabelle `bin`
            directory in `$PATH`

          + or: install references to the Isabelle executables in
            another directory mentioned in `$PATH`, e.g. as follows:
            ```bash
            Isabelle2021-1/bin/isabelle install "$HOME/bin"
            ```

  * Isabelle/Dedukti:

      - Clone the repository:
        ```bash
        git clone https://github.com/Deducteam/isabelle_dedukti.git
        ```

      - Register it to Isabelle as a user component, by providing a
        (relative or absolute) directory name as follows:
        ```bash
        isabelle components -u $path_to_isabelle_dedukti
        ```
        The resulting configuration is in `$ISABELLE_HOME_USER/etc/components`
        (e.g. use Isabelle/jEdit / File Browser / Favorites to get there).

        For historic reasons, there might be some `init_component`
        line in `$ISABELLE_HOME_USER/etc/settings` --- these should be
        removed, to avoid duplicate component initialization.

      - Compile it:
        ```bash
        isabelle scala_build
        ```

  * Dk file checkers:

    - [kocheck](https://github.com/01mf02/kontroli-rs)
    - [dkcheck](https://github.com/Deducteam/Dedukti)
    - [lambdapi](https://github.com/Deducteam/lambdapi)
    
  * Lp file checkers:
  
    - [lambdapi](https://github.com/Deducteam/lambdapi)

  * Patching the Isabelle/HOL library:

    - You may want to start with changing the permission on the HOL folder:

    ```
    chmod -R +w <path to your Isabelle distribution>/src/HOL/
    ```

    - Patch the folder, from the isabelle_dedukti folder:

    ```
    patch -up0 -d <path to your Isabelle distribution>/src/HOL/ < HOL.patch
    ```

    - To reverse the patch:

    ```
    patch -uREp0 -d <path to your Isabelle distribution>/src/HOL/ < HOL.patch
    ```

    - The list of changes can be found in `changes.txt`

  * Deleting the databases:

    - If something goes wrong, you may want to try deleting the databases (which means the proof terms will be rebuilt anew) located somewhere like:

    ```
    $ISABELLE_HOME_USER/Isabelle2021-1/heaps/polyml-<something>/log/
    ```


## Examples

A typical way of calling the tool is as follows for lambdapi format:

```
isabelle dedukti_generate -O main.lp -b -v -r theory session
```

or for dedukti format:

```
isabelle dedukti_generate -O main.dk -b -v -r theory session
```

About the options and inputs:

  * You have the same options as in `dedukti_import`. In particular, you should specify the output format with -o.
  * The two inputs are:
    - First, a theory until which you want to build/translate. Ex: Complex_Main.
    - Second, a usual session to which the first argument belongs. Ex: HOL.
  * The option -b is for building: when specified, a `ROOT` file will be created as follows. The session in second argument will be topologically ordered. Then one session per theory will be created whose parent is the session associated with the predecessor in topological ordering. Finally, the session associated with the first argument will be built (and so all the sessions for the predecessors will be built too). Two additional files (`deps.mk` and `Makefile`) will be generated to check the generated dk files with kocheck.
  * The option -r is for recursive translation: when this option is not specified, only the theory from the first argument will be translated. Otherwise, all predecessors will be translated as well.

To check the lamdbapi format:

```
lambdapi check theory.lp
```

or for the dedukti format (using kocheck):

```
make
```


## What was tested?

  * Building: HOL until Complex_Main, except Quickchecks, Record, Nunchaku and Nitpick (it seems Quickchecks is unsound and should be avoided anyway). Time ~40mins with 16GB memory.
  * Translating/writing: same as above, both for lambdapi and dedukti. Time ~15mins for both lambdapi and dedukti.
  * Checking: No error was found until Transfer but memory blew up with lambdapi. Goes all the way with kocheck.


## Known issues

  * Bit_operations are slow to build because of the way they are defined compared to some simplification rules in Parity. Not fixed.
  * Presburger is slow to build because of the examples at the end. Not fixed.
  * In a database associated with a given theory, there might be proofs labelled from another theory. Fix: those proofs are not too many so they are just translated in this theory.
  * Somehow, the databases for Nat and Sum_type use proofs from Product_Type while they are independent in the dependency graph. Fix: add explictly the connection in the graph. 
  * Quickcheck_random fails to build (it is actually unsound). Fix: remove it from the dependency graph (together with other theories).
  * The -o is used in a awkward way. You just need to call with <something>.lp or <something>.dk, whatever the <something> is.


## Project structure

- `ast.scala` defines the AST of the exported material. It is common for dedukti and lambdapi, and is a (very) strict subset of the ASTs of these languages
- `translate.scala` translates from Isabelle/Pure to the common dedukti/lambdapi AST
- `writers.scala` write out either dedukti output or lambdapi output
- `importer.scala` wraps the previous files into an Isabelle component, defining the CLI and interacting with other components. [Jeremy]: Note it has been changed a lot. It will now create one file by session, because it is expected to be ran on a single-theory session. However, the ancestor of this session does not need to be Pure, and nothing from previous theories will be translated.
- `generator.scala` wraps the previous files into an Isabelle component, creating a ROOT file, building, calling the translator and postprocessing the output file
- `tools.scala` defines the `isabelle dedukti_import` and `isabelle dedukti_generate` command-line tools, which is registered via `services` in `etc/build.props`


## Isabelle development and browsing of sources

* Note: Without proper IDE support Isabelle sources are very hard to
  read and write. (Emacs or vi are not a proper IDE.)

* Isabelle/ML: use Isabelle/jEdit and open ML files (with their proper
  `.thy` file opened as well), but for Isabelle/Pure a special
  bootstrap theory context is provided by
  `$ISABELLE_HOME/src/Pure/ROOT.ML` (see Documentation panel).

* Isabelle/HOL: use Isabelle/Pure to process the theory and ML sources
  in Isabelle/jEdit, e.g. like this:
  ```bash
  isabelle jedit -l Pure
  ```
  then open `$ISABELLE_HOME/src/HOL/Main.thy` via File Browser / Favorites

* Isabelle/Scala: use IntelliJ IDEA with the Java/Scala project generated
  by `isabelle scala_project -L -f`:
  ```bash
  idea "$(isabelle getenv -b ISABELLE_HOME_USER)/scala_project"
  ```
