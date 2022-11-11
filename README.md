# Isabelle component exporting Isabelle proofs to Dedukti

## Dependencies

* [Isabelle2021-1](https://isabelle.sketis.net/website-Isabelle2021-1)

* one dk file checker among:

    - [kocheck](https://github.com/01mf02/kontroli-rs)
    - [dkcheck](https://github.com/Deducteam/Dedukti) 2.7
    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

* or one lp file checker among

    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1


## Prerequisites

  * **Isabelle**

      - Download [Isabelle2021-1](https://isabelle.sketis.net/website-Isabelle2021-1)

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

  * **isabelle_dedukti**

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

  * **Deleting the Isabelle databases**

    - If something goes wrong, you may want to try deleting the databases (which means the proof terms will be rebuilt anew) located somewhere like:

    ```
    $ISABELLE_HOME_USER/Isabelle2021-1/heaps/polyml-<something>/log/
    ```

  * **Patching the Isabelle/HOL library**

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

    - Changes:

        - Main, removed quickcheck and nunchaku
        - Mirabelle removed quickcheck
        - split quickcheck_random --> random_prep
        - split quickcheck_exhaustive --> random_prep
        - HOL/Tools/Quickcheck random_generator, random_fun_lift --> Random_Prep.random_fun_lift
        - random_pred, quickcheck_random --> random_prep
        - predicate_compile, quickcheck_exhaustive --> random_prep
        - HOL/Tools/Predicate_Compile predicate_compile_compilations, Quickcheck_Exhaustive --> Random_Prep (many times)
        - HOL/Tools/Predicate_Compile predicate_compile_core, quickcheck_random --> random_prep (twice), quickcheck_exhaustive --> random_prep (once)
        - record, quickcheck_exhaustive --> random_pred
        - Enum --> rewrite proofs, removed splits
        - Factorial ??
        - List --> rewrite proofs, remove subproofs
        - Rat, Real --> remove nitpick + quickcheck setups
        - String --> rewrite function + proof
        - Transcendental --> rewrite proof to remove arith+
        - MacLaurin --> rewrite proof quite a lot
        - Bit_operations: trying to rewrite some proofs (a problem remains that a simp rule in Parity is of the shape 1 + something while it would be used as something + 1)


## Usage

```
isabelle dedukti_generate -O main.$ext -b -v -r $theory $session
```

where:
- $theory is a theory of the session $session. For instance, the theory `HOL.Groups` in the session `HOL`,
- $ext is either `dk` or `lp`,

This command generates:
- a file `ROOT` (if the option `-b` is given) with the declaration of a session for each theory of $session, in the order of their dependencies,
- a file $theory.$ext containing the transation of $theory and, if the option `-r` is given, a file $theory'.$ext for each $theory' on which $theory depends.

Some details are printed if the option `-v` is given.

Remark: a theory whose name contains a "." is translated to a file where every "." is replaced by "_" because dkcheck does not accept dots in module names.

Remark: [dependency graph the HOL session](https://isabelle.in.tum.de/website-Isabelle2022/dist/library/HOL/HOL/session_graph.pdf)


## Checking the lp output with lambdapi

```
lambdapi check $theory.lp
```


## Checking the dk output with dkcheck

```
dk dep *.dk > deps.mk
make -f dedukti.mk
```


## What was tested?

  * Building: HOL until Complex_Main, except Quickchecks, Record, Nunchaku and Nitpick (it seems Quickchecks is unsound and should be avoided anyway). Time ~40mins with 16GB memory.
  * Translating/writing: same as above, both for lambdapi and dedukti. Time ~26mins for lp, and the same for dk.
  * Checking: No error was found until Transfer but memory blew up with lambdapi. Goes all the way with dkcheck or kocheck.


## Known issues

  * Bit_operations are slow to build because of the way they are defined compared to some simplification rules in Parity. Not fixed.
  * Presburger is slow to build because of the examples at the end. Not fixed.
  * In a database associated with a given theory, there might be proofs labelled from another theory. Fix: those proofs are not too many so they are just translated in this theory.
  * Somehow, the databases for Nat and Sum_type use proofs from Product_Type while they are independent in the dependency graph. Fix: add explictly the connection in the dependency graph.
  * Quickcheck_random fails to build (it is actually unsound). Fix: remove it from the dependency graph (together with other theories).


## Project structure

- `ast.scala` defines the AST of the exported material. It is common for dedukti and lambdapi, and is a (very) strict subset of the ASTs of these languages
- `translate.scala` translates from Isabelle/Pure to the common dedukti/lambdapi AST
- `writers.scala` writes out either dedukti output or lambdapi output
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
