# Isabelle component exporting Isabelle proofs to Dedukti

## Dependencies

* [Isabelle2023](https://isabelle.in.tum.de/website-Isabelle2023/dist/Isabelle2023_linux.tar.gz)

* one dk file checker among:

    - [kocheck](https://github.com/01mf02/kontroli-rs)
    - [dkcheck](https://github.com/Deducteam/Dedukti) 2.7
    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

* or one lp file checker among

    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

## Prerequisites

  * **Isabelle**

      - Download [Isabelle2023](https://isabelle.in.tum.de/website-Isabelle2023/dist/Isabelle2023_linux.tar.gz)

      - Unpack and run `Isabelle2023/bin/isabelle jedit` at least
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

        For historical reasons, there might be some `init_component`
        line in `$ISABELLE_HOME_USER/etc/settings` --- these should be
        removed, to avoid duplicate component initialization.

      - Compile it:
        ```bash
        isabelle scala_build
        ```

  * **Patching the Isabelle/HOL library**

    A few Isabelle/HOL files need to be modified so that exported proofs are of smaller size and that no oracle are used. See the modifications in [HOL.patch](https://github.com/Deducteam/isabelle_dedukti/blob/master/HOL.patch). For now, HOL and HOL-Library are patched.
    
    - You may want to start with changing the permission on the HOL folder:

    ```bash
    chmod -R +w $path_to_Isabelle_dir/src/HOL/
    ```

    - Patch the folder, from the isabelle_dedukti folder:

    ```bash
    patch -up0 -d $path_to_Isabelle_dir/src/HOL/ < HOL.patch
    ```

    - To reverse the patch:

    ```bash
    patch -uREp0 -d $path_to_Isabelle_dir/src/HOL/ < HOL.patch
    ```

    - To update the patch:
    
    ```bash
    cd $path_to_unpatched_Isabelle_dir
    diff -urNx '*~' -x '*.orig' . $path_to_patched_Isabelle_dir/src/HOL > HOL.patch
    ```

  * **Deleting the Isabelle databases**

    If something goes wrong, you may delete the databases (which means the proof terms will be rebuilt anew) located somewhere like:

    ```bash
    $ISABELLE_HOME_USER/Isabelle2023/heaps/polyml-$something/log/
    ```

## How to make Isabelle record proofs?

Isabelle theories are built within sessions, and sessions are defined in files named `ROOT`. A quick way to specify a `ROOT` file to Isabelle is with the `-d` option.

To export proofs from Isabelle so that they can be translated to Dedukti or Lambdapi afterwards, users need to use the following options in the definition of their session:

```
export_theory,export_proofs,record_proofs=2
```

For instance, the following session builds the session HOL with proof recording:
```
session HOL_wp in HOL_wp = Pure +
  options [strict_facts,export_theory,export_proofs,record_proofs=2]
  sessions Tools HOL
  theories
    Main
    Complex_Main
  document_theories
    Tools.Code_Generator
```

Isabelle requires a dedicated directory for each session, specified by the `in HOL_wp` part above. Usually, it suffices to have an empty directory with the same name as the session.

To actually export proof terms from Isabelle, assuming the `ROOT` file containing the session info is located in `$rootdir` do:

```bash
isabelle build -b -d $rootdir $session
```

## Commands to translate Isabelle proofs to Dedukti and Lambdapi

WARNING: the Lambdapi output is temporarily deactivated for it needs to be fixed.

To translate an already built session to Dedukti, do:

```bash
isabelle dedukti_session -d $root_dir $session`
```

Dedukti files are generated in the current directory by default.

Run `isabelle dedukti_session` with no argument to learn more about the available options.

The command `isabelle dedukti_session` generates also a shell script to check the correctness of Dedukti files with `dk check`:
```bash
bash dkcheck_$session.sh
```

Sessions must be built and translated in the order of their dependencies (starting from builtin session Pure).

To translate other sessions, follow these steps:
- add the relevant components to isabelle (for example, AFP),
- define the session:
  - specify the proof export options in your ROOT file
  - make sure that the parent session also exports proofs (otherwise, Isabelle generates unfinished proofs which cannot be translated to Dedukti)
- run the above commands

Remark: to visualize theory dependencies in HOL, you can look at the [dependency graph of the HOL session](https://isabelle.in.tum.de/website-Isabelle2023/dist/library/HOL/HOL/session_graph.pdf).

## Translation to Coq

The generated Dedukti files can be translated to Coq by using the Coq export function of Lambdapi. Example:

```
cd examples
export SESSION=HOL_Nat_wp
time make build
time make dk
time make -j32 v
time make -j32 vo
```

## Performances

Performance on a machine with 32 processors i9-13950HX and 64 Go RAM:

| session                     |   build |  to dk | checking | to coq |      checking |
|:----------------------------|--------:|-------:|---------:|-------:|--------------:|
| Pure                        |         |     3s |          |     0s |            1s |
| HOL_Groups_wp               |    16s? |    10s |      1s? |     0s |           18s |
| HOL_Pre_Enum_wp             | 16m56s? |  9m13s |   5m31s? |  1m58s | out of memory |
| HOL_Enum_wp                 |  1m18s? |    1m? |     18s? |        |               |
| HOL_Quickcheck_Random_wp    |  3m26s? | 6m32s? |   1m50s? |        |               |
| HOL_Quickcheck_Narrowing_wp |    33s? |   43s? |     11s? |        |               |
| HOL_Main                    |    57s? |  2m6s? |     50s? |        |               |
| HOL_Pre_Transcendental_wp   |  2m29s? | 2m24s? |    1m2s? |        |               |
| HOL_Transcendental_wp       |  1m35s? | 2m23s? |     35s? |        |               |
| HOL_wp                      |  4m19s? | 4m51s? |   1m54s? |        |               |


## Project structure

- `ast.scala` provides an AST common to (a strict part of) Dedukti and Lambdapi
- `translate.scala` provides functions to translate Isabelle to the common AST
- `writers.scala` provides functions to generate Dedukti or Lambdapi code
- `exporter.scala` provides the main function to export and translate a session
- `generator.scala` provides the Isabelle command `dedukti_session`
- `rootfile.scala` provides the Isabelle command `dedukti_root`
- `dkcheck.scala` provides the Isabelle command `dedukti_check`

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
