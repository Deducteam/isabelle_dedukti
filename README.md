# Isabelle component exporting Isabelle proofs to Dedukti

## Dependencies

* [Isabelle2025](https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz)

* one dk file checker among:

    - [kocheck](https://github.com/01mf02/kontroli-rs)
    - [dkcheck](https://github.com/Deducteam/Dedukti) 2.7
    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

* or one lp file checker among

    - [lambdapi](https://github.com/Deducteam/lambdapi) >= 2.2.1

## Prerequisites

  * **Isabelle**

      - Download [Isabelle2025](https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025_linux.tar.gz)

      - Unpack and run `Isabelle2025/bin/isabelle jedit` at least
        once, to ensure that everything works (e.g. see Documentation
        panel with Examples).

      - In the following, the command-line executable `isabelle` is used
        instead of the full `Isabelle2025/bin/isabelle`. To be able to use the short version one can:

          + insert the absolute path of the Isabelle `bin`
            directory in `$PATH` ([how to add directories to the $PATH variable](https://gist.github.com/nex3/c395b2f8fd4b02068be37c961301caa7))

          + or install references to the Isabelle executables in
            another directory mentioned in `$PATH`

  * **`isabelle_dedukti`**

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

    A few Isabelle/HOL files need to be modified so that exported proofs are of smaller size and that no oracle are used. See the modifications in [HOL.patch](https://github.com/Deducteam/isabelle_dedukti/blob/master/HOL.patch). For now, only HOL and HOL-Library are patched.

    - Change the permission on the HOL folder:

    ```bash
    chmod -R +w $path_to_Isabelle_dir/src/HOL/
    ```

    - Patch the HOL folder from the `isabelle_dedukti` folder:

    ```bash
    patch -up0 -d $path_to_Isabelle_dir/src/HOL/ < HOL.patch
    ```

    - To reverse the patch:

    ```bash
    patch -uREp0 -d $path_to_Isabelle_dir/src/HOL/ < HOL.patch
    ```

    - To update the patch:
    
    ```bash
    diff -urNx '*~' -x '*.orig' $path_to_unpatched_Isabelle_dir/src/HOL $path_to_patched_Isabelle_dir/src/HOL | sed -e "s|$path_to_unpatched_Isabelle_dir/src/HOL||" -e "s|$path_to_patched_Isabelle_dir/src/HOL||" > HOL.patch
    ```

## How to make Isabelle record proofs?

Isabelle theories are defined within [sessions](https://isabelle.in.tum.de/website-Isabelle2021-1/dist/library/Doc/System/Sessions.html) that must be defined in a file named `ROOT`. A session can extend another session.

To export proofs from Isabelle so that they can be translated to Dedukti or Lambdapi afterwards, users need to use the following options in the definition of their sessions:

```
export_theory,export_proofs,record_proofs=2
```

For instance, the following code defines a session `HOL_wp` extending the builtin session `Pure` for exporting the proofs of the theory file `HOL/Complex_Main.thy`:
```
session HOL_wp = Pure +
  options [strict_facts,export_theory,export_proofs,record_proofs=2]
  sessions Tools HOL
  theories
    Main
    Complex_Main
  document_theories
    Tools.Code_Generator
```

As an example, the file [`examples/ROOT`](https://github.com/Deducteam/isabelle_dedukti/blob/master/examples/ROOT) defines various sessions with proof recording.

The proofs of a session can then be built by using the following Isabelle command:
```bash
isabelle build -b -d$root_file_dir $session
```

This also builds any parent session that has not been built yet.

Remark: to visualize theory dependencies in HOL, you can look at the [dependency graph of the HOL session](https://isabelle.in.tum.de/website-Isabelle2025/dist/library/HOL/HOL/session_graph.pdf).

## Command to translate Isabelle proofs to Dedukti

To translate to Dedukti an already built session whose parent session has already been translated, do:

```bash
isabelle dedukti_generate -d $root_dir $session`
```

To automatically translation parent sessions as well, use the option `-r`.

For the translation to work, follow these steps:
- add the relevant components to Isabelle (for example, AFP),
- add the proof export options in your ROOT file,
- make sure that the parent sessions also export proofs (otherwise, Isabelle will generate incomplete proofs which cannot be translated to Dedukti).

## `examples/Makefile`

The `examples` directory contains a `Makefile` that provides various targets automating the building and the translation of an Isabelle session specified by an argument of the form `SESSION=$session`:
- build: makes Isabelle export the proofs
- dk: translates Isabelle proofs to Dedukti files
- dko: checks the obtained Dedukti files
- lp: translates Isabelle proofs to Lambdapi files
- lpo: checks the obtained Lambdapi files
- v: translates the Lambdapi files to Rocq
- vo: checks the obtained Rocq files

To check a translated session, make sure to translate all its parent sessions first (including Pure).

Find out all the possible targets and variables that can be setup by running `make` with no arguments.

Remark: the translation to Lambdapi and Rocq is still work in progress.

## Performances

Performance on a machine with 32 processors i9-13950HX and 64 Go RAM
(but multiprocessing is used in v and vo only for the moment):

| SESSION                        | build | db size |    dk | dk size | dko |  v |    vo |   lpo |
|:-------------------------------|------:|--------:|------:|--------:|----:|---:|------:|------:|
| Pure                           |    2s |       0 |    2s |     60K |  0s | 0s |    1s |    3s |
| HOL\_Groups\_wp                |   15s |      7M |   12s |     11M |  1s | 0s |   15s |    3s |
| HOL\_Nat\_wp                   |   53s |     19M |  1m4s |    107M | 12s | 2s | 3m26s |   28s |
| HOL\_BNF\_Def\_wp              | 1m41s |     29M | 2m36s |    328M | 40s | 7s | 13m4s | 1m37s |
| HOL\_Int\_wp                   | 1m53s |     33M | 2m15s |    239M |     |    |       |       |
| HOL\_Set\_Interval\_wp         | 2m40s |     45M | 8m35s |      1G |     |    |       |       |
| HOL\_Presburger\_wp            | 2m25s |     42M | 7m26s |      1G |     |    |       |       |
| HOL\_List\_wp                  | 6m53s |     46M |       |         |     |    |       |       |
| HOL\_Enum\_wp                  |       |         |       |         |     |    |       |       |
| HOL\_Quickcheck\_Random\_wp    |       |         |       |         |     |    |       |       |
| HOL\_Quickcheck\_Narrowing\_wp |       |         |       |         |     |    |       |       |
| HOL\_Main\_wp                  |       |         |       |         |     |    |       |       |
| HOL\_Pre\_Transcendental\_wp   |       |         |       |         |     |    |       |       |
| HOL\_Transcendental\_wp        |       |         |       |         |     |    |       |       |
| HOL\_Complex\_Main\_wp         |       |         |       |         |     |    |       |       |

There is room for many important improvements. Makarius Wenzel is working on improving the export of proof terms in Isabelle. The generation of dk files is not modular. No term sharing is currently used in dk and v files.

## Description of each scala file in the src directory (in dependancy order)

- ast.scala: Syntax of dk/lp terms, notations and commands in scala (Only those that are needed)
- translate.scala: Functions to translate Isabelle objects to the syntax from ast.scala
- writers.scala: Functions to read objects in the syntax from ast.scala and write them to dk or lp files in the correct manner
- exporter.scala: Exporter.exporter translates an Isabelle session to a dk or lp file
- generator.scala: Generator.generator reads (and potentially translates) all parent sessions of an Isabelle session before translating that session with Exporter.exporter
- tool.scala: exports Generator.generator as an Isabelle command for the command line (`isabelle dedukti_translate`)

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
