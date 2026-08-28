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

The main refinement theorem is
`Chess.legalMoves_correct`: filtering the transparent candidate universe is
extensionally equal to the declarative `Chess.legalMove` relation.  The
registry-facing `ChessKernel.main_result` exposes that theorem through the
small `Challenge.lean` / proved `Solution.lean` split.  `Chess.kernel_correct`
collects that result with the notation, perft, special-move, symmetry, and
mate-certificate checks.

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

`Challenge.lean` contains only the advertised statement. `Solution.lean`
proves the same declaration from the completed library. `comparator.json`
pins the declaration checked by Palomar Comparator, while `formalization.yaml`
records scope, provenance, authorship, automation, and review status.

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
proved generator correspondence and checked concrete result families. It does
not claim that every theorem name in the Isabelle entry has a one-for-one Lean
counterpart.

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
