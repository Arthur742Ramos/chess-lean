# Chess in Lean 4

This repository is a standalone Lean 4 reimplementation of the chess kernel
in the Isabelle/HOL development
[`isabelle-afp-monorepo/projects/chess-isabelle`](https://github.com/Arthur742Ramos/isabelle-afp-monorepo/tree/master/projects/chess-isabelle).
It has no Isabelle runtime dependency.

Authors: Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz.

## What is formalized

The development models orthodox chess with total, executable state
transitions:

- finite `Fin 8` board coordinates, pieces, positions, clocks, castling rights,
  and en-passant state;
- geometric attacks, check, pseudo-legal moves, legal moves, special moves,
  and an exhaustive finite candidate generator;
- histories, reachability, repetition keys, claimable and automatic draw
  predicates, terminal game status, and bounded forced mate;
- recursively checked mate certificates, including the Isabelle mate-in-two
  showcase;
- typed and strict textual six-field FEN, UCI, and canonical SAN interfaces;
- perft, rank-reflection symmetry, and concrete executable regression tests.

The selected registry result is the production theorem
`Chess.legalMoves_correct`: for every full `Chess.Position` and every full
`Chess.Move`, membership in the exhaustive candidate generator is equivalent
to the declarative legal-move relation.  The state includes castling rights
and en-passant targets; the move type includes normal moves, promotions,
en-passant captures, and all four castling moves.  `Challenge.lean` and
`Solution.lean` carry a standalone copy of this complete rule-kernel surface
so Palomar can compare the theorem without importing the repository's local
`.olean` files.  The Solution contains the same production proof.  The
separate `Chess.kernel_correct` theorem collects this generator result with
the notation, perft, special-move, symmetry, and mate-certificate checks.

## Verified reference results

The native-evaluated regression suite checks:

- initial legal moves `20`, and perft depths `1`, `2`, and `3` equal to
  `20`, `400`, and `8902`;
- Kiwipete perft depths `1` and `2` equal to `48` and `2039`;
- the standard en-passant/promotion-rich position at depths `1`, `2`, and
  `3` equal to `14`, `191`, and `2812`;
- legal castling, en-passant capture, promotion, FEN, UCI, SAN, and reflected
  initial-position checks;
- the seven-reply, three-ply certificate for the concrete two-move mate in
  `Chess/MateTwo.lean`.

These counts are correctness regressions for a transparent reference kernel,
not a claim of engine-grade performance.

## Repository layout

`Chess/Basic.lean`, `Geometry.lean`, `Attacks.lean`, `Check.lean`,
`Transition.lean`, `Legality.lean`, and `Generator.lean` form the rule kernel.
`History.lean`, `Game.lean`, `Perft.lean`, `Mate.lean`, and `Certificates.lean`
add history-aware game semantics. `FEN.lean`, `FENText.lean`, `Notation.lean`,
and `SAN.lean` provide interchange layers. `Symmetry.lean`, `Examples.lean`,
`MateTwo.lean`, and `Kernel.lean` provide the checked extensions and public
correctness bundle.

`Challenge.lean` contains the self-contained full rule-kernel statement and
its deliberate proof placeholder. `Solution.lean` repeats the same
production-faithful rule kernel and proves `Chess.legalMoves_correct`.
`comparator.json` pins that exact production theorem, while
`formalization.yaml` records scope, provenance, authorship, automation, and
review status.

## Build and verify

The project pins Lean `v4.32.0` and Mathlib `v4.32.0` in the checked-in Lake
configuration.

```text
lake exe cache get
lake build
(cd docbuild && lake build Chess:docs)
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

Generated `.lake/` directories and documentation output are intentionally not
part of the submission snapshot. The root license is Apache-2.0.

## Provenance and review boundary

The Isabelle entry is the source formalization being adapted; this repository
is a fresh Lean implementation rather than a mechanically translated copy.
The executable Boolean checker is used for finite computation, while exact
logical predicates such as the unbounded dead-position definition remain
separate from code generation. The current Lean capstone advertises the
proved full-rule generator correspondence and checked concrete result
families. It does not claim that every theorem name in the Isabelle entry has
a one-for-one Lean counterpart.

Palomar submission is a separate action from local validation, CI, and local
review. The exact public commit, Comparator configuration, author relationship,
and review evidence must be recorded before intake; this repository is not
submitted automatically by its build scripts. Once those materials are ready,
use the [Palomar submission form](https://submit.palomar-registry.org/).

## Acknowledgements

The formalization uses Lean 4 and Mathlib. The original Isabelle development
uses Isabelle/HOL and follows the FIDE Laws of Chess, FEN, UCI, SAN, and
standard perft conventions. AI assistance was used for proof engineering; the
final definitions, statements, and proofs in this repository are checked by
Lean.
