# Isabelle/Dedukti

Isabelle component for dedukti.


## Prerequisites

  * Standard OS platform: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * Suitable Isabelle repository clone (see also https://isabelle.in.tum.de/repos/isabelle/file/tip/README_REPOSITORY):

        hg clone https://isabelle.in.tum.de/repos/isabelle
        hg up -r 68d2c533db9c

        isabelle/bin/isabelle components -I
        isabelle/bin/isabelle components -a
        isabelle/bin/isabelle jedit -b


## Settings

Init Isabelle/Dedukti component in `$ISABELLE_HOME_USER/etc/settings` like this:
```
init_component ".../isabelle_dedukti"
```

where `.../isabelle_dedukti` is a local working directory of this repository and `ISABELLE_HOME_USER` the location reported by `isabelle getenv ISABELLE_HOME_USER` (e.g. `$HOME/.isabelle` on Unix).


## Build and test

```
isabelle dedukti_build && isabelle dedukti_test
```


## Examples

### Batch mode
```
isabelle dedukti_import FOL-ex
isabelle dedukti_import -o record_proofs=2 -D.
```


### Interaction

```
isabelle jedit -d. -l Dedukti_Base Ex/Ex_HOL.thy
```
