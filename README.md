# Chess in Lean 4

This repository is a standalone Lean 4 reimplementation of the chess kernel
in the Isabelle/HOL development. A complete copy of the Isabelle source is
also committed here as the public artifact
[`artifacts/isabelle/chess-isabelle`](artifacts/isabelle/chess-isabelle/).
That artifact was exported from `Arthur742Ramos/isabelle-afp-monorepo` at the
immutable Isabelle revision `a81eecf7b7a77064380bdf1f8915d73ee9955fa3`, under
the upstream commit-relative path `projects/chess-isabelle`. It has no
Isabelle runtime dependency at Lean build time.

Authors: Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz.

## What is formalized

The development models orthodox chess rules with total, executable state
transitions over generalized finite position records:

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

`Chess.Position` is an ordinary total record, not a subtype of positions known
to be reachable from the initial position.  It can therefore represent
malformed or unreachable records (for example, records with unusual material,
king placement, clocks, or metadata).  The development defines
`positionInvariant` as a structural safety predicate, but the selected
registry theorem does not assume that predicate or reachability.

The selected registry result is the production theorem
`Chess.legalMoves_correct`: for every full `Chess.Position` record—including
potentially malformed or unreachable records—and every full `Chess.Move`,
membership in the exhaustive candidate generator is equivalent to the
declarative legal-move relation defined by this development.  The state
includes castling rights and en-passant targets; the move type includes normal
moves, promotions, en-passant captures, and all four castling moves.
`Challenge.lean` and `Solution.lean` carry a standalone copy of this complete
rule-kernel surface so Palomar can compare the theorem without importing the
repository's local `.olean` files.  The Solution contains the same production
proof.  The separate `Chess.kernel_correct` theorem collects this generator
result with the notation, perft, special-move, symmetry, and mate-certificate
checks.

This is a correspondence theorem for the represented generalized record
space, not a claim that every record is a legal FIDE position and not a
reachability characterization.  The initial position and the concrete
reference positions used by the perft and notation regressions are orthodox
instances of that broader domain.

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

`Challenge.lean` contains the self-contained generalized-record rule-kernel
statement and its deliberate proof placeholder. `Solution.lean` repeats the
same production-faithful rule kernel and proves `Chess.legalMoves_correct`.
`comparator.json` pins that exact production theorem, while
`formalization.yaml` records scope, provenance, authorship, automation, and
review status. The complete adapted Isabelle source snapshot is preserved in
`artifacts/isabelle/chess-isabelle/`, including its `ROOT`, theory files,
blueprint files, and document sources.

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

The mathematical rules baseline is the FIDE Laws of Chess effective 1 January
2023. The earlier Isabelle/HOL entry is the related formalization adapted by
this Lean development, and its complete source is included in this repository at
`artifacts/isabelle/chess-isabelle/`. The exact source inspected for this port
is revision `a81eecf7b7a77064380bdf1f8915d73ee9955fa3` of
`Arthur742Ramos/isabelle-afp-monorepo`, at the upstream commit-relative path
`projects/chess-isabelle`. The local artifact is the reviewable provenance
snapshot; no access to the upstream repository is required to inspect it.
This repository is a fresh Lean implementation rather than a mechanically
translated copy.
The executable Boolean checker is used for finite computation, while exact
logical predicates such as the unbounded dead-position definition remain
separate from code generation. The current Lean capstone advertises the
proved full-rule generator correspondence over generalized position records
and checked concrete result families.  It does not claim that every theorem
name in the Isabelle entry has a one-for-one Lean counterpart, that arbitrary
records are reachable chess positions, or that the selected theorem itself
enforces orthodox-position well-formedness.

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
