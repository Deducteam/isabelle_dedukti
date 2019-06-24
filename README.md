# Isabelle/Dedukti

Isabelle component for dedukti.


### Prerequisites

  * Standard OS platform: Linux, macOS, Windows (e.g. with Cygwin terminal)

  * Suitable Isabelle version (repository clone), see also https://bitbucket.org/makarius/isabelle-cachan/src/tip/README_REPOSITORY


### Settings

Init Isabelle/Dedukti component in `$ISABELLE_HOME_USER/etc/settings` like this:
```
init_component ".../isabelle_dedukti"
```

where `.../isabelle_dedukti` is a local working directory of this repository and `ISABELLE_HOME_USER` the location reported by `isabelle getenv ISABELLE_HOME_USER` (e.g. `$HOME/.isabelle` on Unix).


### Build

```
isabelle dedukti_build
```


### Run

```
isabelle dedukti_import FOL-ex
isabelle dedukti_import -o record_proofs=2 -D.
```
