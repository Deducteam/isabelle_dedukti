All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## December 2023

- Update to Isabelle 2023 and improvements (Akihisa Yamada)

## November 2023

Update to Isabelle 2022 (Frédéric Blanqui, Jérémy Dubut, Akihisa Yamada)

## October 2022

Improvements (Frédéric Blanqui, Jérémy Dubut, Akihisa Yamada)

## November 2021

### Modular export of all Isabelle/HOL standard library (Jérémy Dubut, Akihisa Yamada and Frédéric Blanqui)

- patch Isabelle/HOL standard library
- introduce command isabelle dedukti_generate
- creates a ROOT file with a session for each theory
- fix Dedukti and Lambapi outputs
- make Dedukti output modular

### Use Isabelle 2021-1 (Makarius Wenzel)

### Code factorisation, improvement and update (Yann Leray)

- Update translator to 2021-03 lambdapi syntax
- Escaping :ddd identifiers
- Add infix symbols, unicode glyphs
- Add notation-less lambdapi output
- Include new wrapped operator syntax
- No more useless disambiguation, better detection of can be implicit arg
- Fix for bound variables
- eta-contract
- Add possibility of skipping eta flag (not final) and add documentation
- Describe project structure
- Enable Github Actions
- Fix proofboxes in wrong files (doesn't scale well)
- Dedukti output fix
- Add patch to remove enum's proofs
- Add patch to remove String's proofs
- Some more comments
- Reach the limits of eta_expansion
- Only write optional arguments if no other argument follows
- Update to Isabelle-2021-1-RC1 by Makarius Wenzel

## March-June 2021

Improvements (Makarius Wenzel)

## April 2020

Use Isabelle 2020 (Makarius Wenzel)

## February-March 2020

Improvements (Makarius Wenzel)

## October 2019

Add Lambdapi output (Michael Färber)

## July-November 2019

Improvements (Makarius Wenzel)

## June 2019

First version (Makarius Wenzel)
