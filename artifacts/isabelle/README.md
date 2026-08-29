# Vendored Isabelle/HOL artifact

This directory contains the complete Isabelle/HOL chess formalization used as
the source artifact for the Lean reimplementation in this repository. The
snapshot was exported from `Arthur742Ramos/isabelle-afp-monorepo` at immutable
revision `a81eecf7b7a77064380bdf1f8915d73ee9955fa3`, from the commit-relative
project path `projects/chess-isabelle`.

The reviewable copy is `chess-isabelle/`. It includes the Isabelle session
`ROOT`, all theory sources, the project README and blueprint files, and the
document sources. The upstream repository is not required to inspect this
artifact. The Lean development remains independently buildable and does not
import Isabelle files at Lean build time.

The corresponding provenance and adaptation relationship are recorded in the
repository's `formalization.yaml`.
