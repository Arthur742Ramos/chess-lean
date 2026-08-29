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
`positionInvariant` as a structural safety predicate and proves that legal
reachability from the initial position preserves it.

The selected registry result is `Chess.reachable_positionInvariant`.  It proves
by induction on the reflexive-transitive closure of legal chess transitions
that every reachable position has exactly one king of each colour, no pawn on
either promotion rank, castling rights consistent with the home king and rook,
and a positive fullmove clock.  The transition step is proved separately for
normal moves, promotions, en-passant captures, and all four castling moves;
the proof also accounts for the rights-removal bookkeeping.  `Challenge.lean`
and `Solution.lean` carry the same standalone surface so Palomar can compare
the result without importing the repository's local `.olean` files.  The
certificate-adequacy theorem remains proved as an internal result, and
`Chess.kernel_correct` collects the generator, notation, perft, special-move,
symmetry, and certificate checks.

This is a one-way safety theorem: it does not claim that every structurally
invariant record is reachable, nor that every represented record is a legal
FIDE position. The initial position and the concrete reference positions used
by the perft and notation regressions are orthodox instances of the broader
total record domain.

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
  `Chess/MateTwo.lean`, accepted by both certificate checkers and yielding the
  corresponding `ruleForcedMate` theorem.

These counts are correctness regressions for a transparent reference kernel,
not a claim of engine-grade performance.

## Repository layout

`Chess/Basic.lean`, `Geometry.lean`, `Attacks.lean`, `Check.lean`,
`Transition.lean`, `Legality.lean`, and `Generator.lean` form the rule kernel.
`History.lean`, `Game.lean`, `Perft.lean`, `Mate.lean`, and `Certificates.lean`
add history-aware game semantics. `FEN.lean`, `FENText.lean`, `Notation.lean`,
and `SAN.lean` provide interchange layers. `Symmetry.lean`, `Examples.lean`,
`MateTwo.lean`, `Invariant.lean`, and `Kernel.lean` provide the checked
extensions and public correctness bundle.

`Challenge.lean` contains the self-contained generalized-record rule kernel
and the deliberate proof placeholder for `Chess.reachable_positionInvariant`.
`Solution.lean` repeats the same production-faithful surface and supplies the
full invariant proof, while also retaining the proved certificate-adequacy and
`Chess.legalMoves_correct` lemmas. `comparator.json` pins the reachability
invariant theorem, while
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
proved reachable-position invariant, together with the full-rule generator
correspondence, certificate adequacy, and checked concrete result families.
The history-aware and draw-aware checker is kept separate because its policy
depends on an explicit history. This repository does not claim that every
theorem name in the Isabelle entry has a one-for-one Lean counterpart, that
arbitrary records are reachable chess positions, or that the invariant is a
complete characterization of reachability.

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
