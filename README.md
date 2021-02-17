# Isabelle/Dedukti

Isabelle component for dedukti.


## Prerequisites

  * Standard OS platform: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * Suitable Isabelle repository clone (see also https://isabelle.in.tum.de/repos/isabelle/file/tip/README_REPOSITORY):

        hg clone https://isabelle.sketis.net/repos/isabelle
        cd isabelle
        hg up -r Isabelle2020
        # add ./bin/isabelle in your $PATH
        isabelle components -I
        isabelle components -a
        isabelle jedit -b
        # install isabelle_dedukti here:
        git clone https://github.com/Deducteam/isabelle_dedukti.git
        
To verify the produced files, you can use either Dedukti or Lambdapi.

  * Dedukti:

        git clone https://github.com/Deducteam/Dedukti
        cd Dedukti
        git checkout 38e0c57c2e29fce9c483fc679e5e3943522f536a
        make && make install

  * Lambdapi:

        git clone https://github.com/Deducteam/lambdapi.git
        cd lambdapi
        git checkout 72d3a1889a9afb7b560c96924236bc63d4cfc141
        make && make install


## Settings

Init Isabelle/Dedukti component in `$ISABELLE_HOME_USER/etc/settings` like this:
```
init_component ".../isabelle_dedukti"
```

where `.../isabelle_dedukti` is a *sub-directory* of the `isabelle` repository, and `ISABELLE_HOME_USER` the location reported by `isabelle getenv ISABELLE_HOME_USER` (e.g. `$HOME/.isabelle` on Unix).


## Build and test

```
isabelle dedukti_build && isabelle dedukti_test
```


## Examples

Generating and checking a Dedukti file:

~~~
isabelle dedukti_import -O output.dk Dedukti_Import
dkcheck --eta output.dk
~~~

Generating and checking a Lambdapi file:

```
isabelle dedukti_import -O output.lp Dedukti_Base
lambdapi output.lp
```

Small-scale proofs with nicer names:

```
isabelle dedukti_import -o export_standard_proofs Dedukti_Base
```
