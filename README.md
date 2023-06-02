# Isabelle component exporting Isabelle proofs to Dedukti

## Dependencies

* [Isabelle2022](https://isabelle.in.tum.de/website-Isabelle2022/dist/Isabelle2022_linux.tar.gz)

* one dk file checker among:

    - [kocheck](https://github.com/01mf02/kontroli-rs)
    - [dkcheck](https://github.com/Deducteam/Dedukti) 2.7
    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

* or one lp file checker among

    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1


## Prerequisites

  * **Isabelle**

      - Download [Isabelle2022](https://isabelle.in.tum.de/website-Isabelle2022/dist/Isabelle2022_linux.tar.gz)

      - Unpack and run `Isabelle2022/bin/isabelle jedit` at least
        once, to ensure that everything works (e.g. see Documentation
        panel with Examples).

      - The command-line executable `isabelle` is subsequently used
        without further qualification, in practice it works like this:

          + explicit executable path (relative or absolute) on the command-line

          + or: insert the absolute path of the Isabelle `bin`
            directory in `$PATH`

          + or: install references to the Isabelle executables in
            another directory mentioned in `$PATH`

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

  * **Patching the Isabelle/HOL library**

    A few Isabelle/HOL files need to be modified so that exported proofs are of smaller size and that no oracle are used. See the modifications in [HOL.patch](https://github.com/Deducteam/isabelle_dedukti/blob/master/HOL.patch).
    
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

    - To create the patch:
    
    ```
    cd path_to_unpatched_Isabelle_dir
    diff -urNx '*~' . path_to_patched_Isabelle_dir/src/HOL > HOL.patch
    ```

  * **Deleting the Isabelle databases**

    If something goes wrong, you may delete the databases (which means the proof terms will be rebuilt anew) located somewhere like:

    ```
    $ISABELLE_HOME_USER/Isabelle2022/heaps/polyml-<something>/log/
    ```

## Provided commands

- `isabelle dedukti_root $session`: generate a ROOT file with a proof-exporting session named Dedukti_$theory for each $theory of $session, and the scripts kocheck.sh and dkcheck.sh to check dk files.

- `isabelle dedukti_session $session [$theory]`: generate a dk or lp file for each theory of $session (up to $theory)

- `isabelle dedukti_theory $theory`: export the specified $theory to a dk or lp file with the same name except that every dot is replaced by an underscore.

Run `isabelle $command` with no argument for more details.

Remark: a theory whose name contains a "." is translated to a dk or lp file where every "." is replaced by "_" because dkcheck does not accept dots in module names.

Remark: [dependency graph of the HOL session](https://isabelle.in.tum.de/website-Isabelle2022/dist/library/HOL/HOL/session_graph.pdf)

## Examples

- Exporting the Isabelle/HOL standard library up to `Groups`:
```
isabelle dedukti_root HOL
isabelle build -b Dedukti_HOL.Groups
isabelle dedukti_session HOL HOL.Groups
isabelle dedukti_session -l HOL HOL.Groups
```
- Exporting the Isabelle/HOL standard library up to `Complex_Main`:
```
isabelle dedukti_root HOL
isabelle build -b Dedukti_Complex_Main
isabelle dedukti_session HOL
isabelle dedukti_session -l HOL
```
- Exporting a single theory:
```
isabelle dedukti_root HOL
isabelle build -b Dedukti_HOL.Groups
isabelle dedukti_theory HOL.Groups
isabelle dedukti_theory -l HOL.Groups
```

## Checking the lp output with lambdapi

```
lambdapi check Dedukti_HOL_Groups.lp
```

## Checking the dk output with dkcheck

```
bash ./dkcheck.sh
```

## Checking the dk output with kocheck

The verification of dk files by kocheck requires to slightly modify those files because kocheck does not accept require commands and self-qualified identifiers.

```
./remove-requires.sh *.dk
cd kocheck
bash ../kocheck.sh
```

## What was tested?

The whole HOL session can be exported and checked:
  * `isabelle dedukti_root HOL`: 2s
  * `isabelle build -b Dedukti_Complex_Main`: 51m40s, 249 Mo
  * `isabelle dedukti_session HOL`: 20m38s
  * `isabelle dedukti_session -l HOL`: idem
  * `bash kocheck.sh`: 3m
  * `bash dkcheck.sh`: 10m
  * `lambdapi check Complex_Main.lp`: out of memory
  * `lambdapi check HOL_Nat.lp`: 2m04s
  * `lambdapi check HOL_Int.lp`: 11m44s

## Known issues

  * In a database associated with a given theory, there might be proofs labelled from another theory. Fix: those proofs are not too many so they are just translated in this theory.
  * Somehow, the databases for `Nat` and `Sum_type` use proofs from `Product_Type` while they are independent in the dependency graph. Fix: add explictly the connection in the dependency graph.

## Project structure

- `ast.scala` provides an AST common to Dedukti and Lambdapi (it is strict subset of these languages)
- `translate.scala` translates Isabelle/Pure to the common Dedukti and Lambdapi AST
- `writers.scala` writes out an AST to either Dedukti or Lambdapi code
- `exporter.scala` provides the isabelle command `dedukti_theory`
- `generator.scala` provides the Isabelle command `dedukti_session`
- `rootfile.scala` provides the Isabelle command `dedukti_root`

## Browsing and modifying Isabelle sources

Without proper IDE support Isabelle sources may be very hard to read
and write.

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
