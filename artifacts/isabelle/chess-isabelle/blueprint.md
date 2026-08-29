# Chess in Isabelle/HOL: A Verified Executable Semantics

This blueprint plans a self-contained AFP entry implementing orthodox chess as
an executable Isabelle/HOL semantics.  Its intellectual spine is a declarative
legal-move relation, an independently defined exhaustive finite reference
generator proved sound and complete for that relation, and preservation of the
proved core position invariant by every legal transition.  The generator is
deliberately a transparent correctness kernel, not an engine-strength
piece-directed implementation.  The entry additionally covers
history-dependent draws, textual and typed FEN, UCI and canonical SAN notation,
forced mate, certificate checking, reflection/attack symmetry, perft, and
executable examples.

The rules baseline is the English FIDE Laws of Chess effective 1 January 2023,
Articles 1--5 and 9 and Appendix C.  Physical play, clocks, touch-move,
resignation, draw offers, arbiter procedure, Chess960, variants, engine search,
evaluation, openings, ratings, and tablebases are out of scope.  Claimable and
automatic draws are kept distinct.  FEN and UCI are interoperability layers,
not claims that those notations are FIDE standards.

The nodes below are the checked delivery map.  Each `formal` status records
the current Isabelle fact audit: `proved` means a logical proof with no
evaluator oracle, while `tainted` records a finite kernel-evaluation theorem
kept deliberately visible as a regression certificate.  Fact names and theory
names are fixed so later agents and reviewers can work against stable
interfaces.

## Design constraints

* Use finite datatypes for files and ranks and a total board function
  `square \<Rightarrow> piece option`; prove the executable enumeration instead
  of trusting an ad-hoc coordinate encoding.
* Separate structural well-formedness, semantic position invariants, and
  reachability from the initial position.  `position_invariant` is a preserved
  structural safety layer, while `legal_position` is reachability; arbitrary
  puzzle and FEN positions need not be reachable.
* Define attack independently of legal moves.  In accordance with FIDE 3.1.3
  and 3.9.1, a pinned piece still attacks geometrically.
* Make `apply_move` a total deterministic function whose intended use is
  guarded by `pseudo_legal` or `legal_move`; prove field-by-field transition
  laws rather than hiding updates inside an option monad.
* Define legal moves declaratively, then enumerate a finite move universe and
  filter it.  Soundness and completeness must not be true merely by definition.
* Use a canonical repetition key.  Raw FEN equality is insufficient because
  clocks are irrelevant and an en-passant target matters only when the right
  changes the legal possibilities.
* Give forced mate a precise bounded-ply semantics over a history with attacker
  existential choices, defender universal choices, and terminal draws treated
  as failure.  Parameterize the recursive checker by its terminal predicate so
  semantic dead-position reachability is never misrepresented as executable.

## I. Finite board foundation

::: definition {#def-chess-types}
title: Colours, piece kinds, files, ranks, squares, and pieces
isabelle:
  theory: Chess_Square
  fact: all_squares_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Introduce finite datatypes for `color`, `piece_kind`, `file`, and `rank`, the
product type `square`, and the `piece` record.  Define colour opposition,
promotion kinds, square colour, and canonical lists of files, ranks, and
squares.
:::

::: theorem {#thm-board-finiteness}
title: Complete duplicate-free enumeration of the 64 squares
uses:
  - def-chess-types
isabelle:
  theory: Chess_Square
  fact: all_squares_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove `set all_squares = UNIV`, `distinct all_squares`, and
`length all_squares = 64`, together with the corresponding eight-element facts
for files and ranks and executable equality instances for all finite types.

## Proof

Expand the datatype enumerations, discharge membership by cases on file and
rank, and use the product-list distinctness and length lemmas.
:::

::: definition {#def-coordinates}
title: Executable coordinate view
uses:
  - def-chess-types
isabelle:
  theory: Chess_Square
  fact: coords_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Map squares to bounded integer coordinates and provide a partial inverse from
coordinates, avoiding arithmetic on datatype constructors in later geometry.
:::

::: theorem {#thm-coordinate-roundtrip}
title: Coordinate conversion round trips and bounds
uses:
  - def-coordinates
  - thm-board-finiteness
isabelle:
  theory: Chess_Square
  fact: square_of_coords_coords
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove both round-trip directions on the 8-by-8 domain, injectivity of `coords`,
and exact coordinate bounds.

## Proof

Split the square into file and rank and use exhaustive datatype cases for the
forward direction; derive injectivity from the two component inverses.
:::

::: definition {#def-board}
title: Boards and basic queries
uses:
  - def-chess-types
isabelle:
  theory: Chess_Board
  fact: occupied_by_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define `board = square \<Rightarrow> piece option`, `piece_at`, `empty`,
`occupied`, `occupied_by`, `squares_of`, `pieces_of`, updates, moves, and
captures.  Establish extensionality and finite counting lemmas.
:::

::: definition {#def-position}
title: Complete position state
uses:
  - def-board
isabelle:
  theory: Chess_Position
  fact: initial_position_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define castling rights as a dedicated finite datatype and record board, side to
move, rights, en-passant target, halfmove clock, and fullmove number.  State
which fields are game-semantic and which are notation metadata.
:::

::: definition {#def-position-invariant}
title: Layered board and position invariants
uses:
  - def-position
  - def-piece-attacks
isabelle:
  theory: Chess_Position
  fact: position_invariant_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Separate `well_formed_board`, `position_invariant`, and `legal_position`.
The current proved invariant includes exactly one king of each colour, no pawn
on a promotion rank, castling-right consistency, and a positive fullmove
number.  `legal_position` means reachability from the standard initial
position; richer FIDE legality conditions remain explicit extension points.
:::

::: definition {#def-initial-position}
title: Standard initial position
uses:
  - def-position-invariant
isabelle:
  theory: Chess_Position
  fact: initial_position_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define the orthodox initial placement, White to move, all four castling rights,
no en-passant target, zero halfmove clock, and fullmove number one.
:::

::: theorem {#thm-initial-invariant}
title: Initial position satisfies the complete invariant
uses:
  - def-initial-position
isabelle:
  theory: Chess_Position
  fact: initial_position_invariant
  session: Chess
status:
  blueprint: reviewed
  formal: tainted
  agent: ready

The standard initial placement satisfies every clause of `position_invariant`.

## Proof

Evaluate the finite placement and rights tables, normalize the cardinalities,
and discharge king safety from the attack geometry of the blocked back ranks.

:::

## II. Geometry and attacks

::: definition {#def-board-geometry}
title: Rank, file, diagonal, direction, distance, and betweenness
uses:
  - def-coordinates
isabelle:
  theory: Chess_Geometry
  fact: between_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define the declarative geometry of aligned squares, strict betweenness, rays,
and Chebyshev and taxicab distances using coordinates.
:::

::: definition {#def-between-enumerator}
title: Executable squares-between enumerator
uses:
  - def-board-geometry
isabelle:
  theory: Chess_Geometry
  fact: squares_between_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Enumerate, in source-to-destination order, exactly the strict intermediate
squares of an aligned rook or bishop ray; return the empty list off a ray.

:::

::: theorem {#thm-between-correct}
title: Squares-between enumeration is exact and symmetric
uses:
  - def-between-enumerator
isabelle:
  theory: Chess_Geometry
  fact: squares_between_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove membership iff strict geometric betweenness, duplicate-freedom, endpoint
exclusion, and reversal under swapping endpoints.  Derive symmetry of
`clear_between`.

## Proof

Case-split on the eight ray directions.  Reduce list membership to bounded
integer steps, then use reversal of the step interval for symmetry.
:::

::: definition {#def-piece-geometry}
title: Declarative movement geometry for every piece kind
uses:
  - def-board-geometry
isabelle:
  theory: Chess_Geometry
  fact: piece_geometry_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define rook, bishop, queen, knight, king, and colour-sensitive pawn move and
attack geometry.  Pawn attacks are intentionally distinct from pawn advances.
:::

::: definition {#def-piece-attacks}
title: Geometric piece attack relation
uses:
  - def-board
  - def-piece-geometry
  - thm-between-correct
isabelle:
  theory: Chess_Attacks
  fact: piece_attacks_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define attacks from an occupied source, with ray blocking for sliders, pawn
capture geometry, and king adjacency.  Do not impose the attacking side's king
safety: pinned pieces still attack for check and castling purposes.
:::

::: definition {#def-attack-enumerator}
title: Executable attacked-square enumeration
uses:
  - def-piece-attacks
  - thm-board-finiteness
isabelle:
  theory: Chess_Attacks
  fact: attacked_squares_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Collect the squares attacked by every piece of a selected colour in a stable,
duplicate-free order suitable for executable check and castling tests.

:::

::: theorem {#thm-attack-enumerator-correct}
title: Attack enumeration is sound and complete
uses:
  - def-attack-enumerator
isabelle:
  theory: Chess_Attacks
  fact: attacked_squares_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove that membership in `attacked_squares p c` is equivalent to existence of
a piece of colour `c` satisfying `piece_attacks`.

## Proof

Rewrite the finite concatenation over `all_squares`, use board-enumeration
completeness, and apply the per-piece geometry characterization.
:::

## III. Moves and deterministic transition semantics

::: definition {#def-move}
title: Explicit move datatype
uses:
  - def-chess-types
isabelle:
  theory: Chess_Move
  fact: move_distinct_cases
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Use distinct constructors for ordinary moves, promotion, en passant, and each
castling side.  Define source, destination, moving colour where applicable,
capture classification, pawn-move classification, and a canonical order.
:::

::: definition {#def-move-universe}
title: Finite candidate-move universe
uses:
  - def-move
  - thm-board-finiteness
isabelle:
  theory: Chess_Move
  fact: candidate_moves_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Enumerate every ordinary source/destination pair, all four legal promotion
kinds for every pair, en-passant candidates, and four castling constructors.
:::

::: theorem {#thm-move-universe-complete}
title: Candidate-move universe is complete and duplicate-free
uses:
  - def-move-universe
isabelle:
  theory: Chess_Move
  fact: candidate_moves_complete
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Every value of the finite `move` datatype occurs exactly once in the canonical
candidate list.

## Proof

Use cases on the move constructor, square-enumeration completeness, and the
four-element promotion-kind enumeration; prove disjointness by constructors.

:::

::: definition {#def-castling-pseudo}
title: Castling prerequisites
uses:
  - def-piece-attacks
  - def-position
isabelle:
  theory: Chess_Castling
  fact: pseudo_legal_castle_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Require the right, king and rook on their orthodox source squares, clear
intervening squares, and the correct side to move.  Safety of the source,
transit, and destination king squares is stated separately so it cannot be
accidentally reduced to safety only after the move.
:::

::: theorem {#thm-castling-safety}
title: Legal castling begins, crosses, and ends outside attack
uses:
  - def-castling-pseudo
  - def-apply-move
  - def-legal-move
isabelle:
  theory: Chess_Castling
  fact: legal_castle_safe_squares
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

A legal castle implies that the king's source, transit, and destination squares
are not attacked by the opponent, and the resulting position is king-safe.

## Proof

Eliminate the castle constructor from `legal_move`, unfold the three explicit
safety tests, and simplify the king and rook updates in the result board.

:::

::: definition {#def-en-passant-pseudo}
title: En-passant prerequisites
uses:
  - def-position
  - def-piece-geometry
isabelle:
  theory: Chess_En_Passant
  fact: pseudo_legal_en_passant_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Require a correctly ranked capturing pawn, adjacent opponent pawn, empty target,
and the position's one-ply en-passant target.  Reachability will justify that
the target came from the immediately preceding double pawn move.
:::

::: theorem {#thm-en-passant-effect}
title: En-passant removes exactly the bypassed pawn
uses:
  - def-en-passant-pseudo
  - def-apply-move
isabelle:
  theory: Chess_En_Passant
  fact: apply_en_passant_board
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Include the discovered-check edge case: king safety is evaluated on the board
after both the moving pawn and the captured pawn have left their old squares.

## Proof

Expand the en-passant transition and prove extensional board equality by square
cases: source, target, captured-pawn square, and every unaffected square.
:::

::: definition {#def-promotion-pseudo}
title: Promotion and promotion-capture prerequisites
uses:
  - def-piece-geometry
isabelle:
  theory: Chess_Promotion
  fact: pseudo_legal_promotion_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Permit exactly queen, rook, bishop, or knight promotion on the final rank, both
with and without capture.  Reject pawn/king promotion and reject an ordinary
pawn move that ends on the final rank.
:::

::: theorem {#thm-promotion-kind}
title: Legal promotions produce exactly an allowed non-pawn piece
uses:
  - def-promotion-pseudo
  - def-apply-move
  - def-legal-move
isabelle:
  theory: Chess_Promotion
  fact: legal_promotion_kind
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

If a promotion is legal, its replacement kind belongs to
`{Queen, Rook, Bishop, Knight}`, the destination is the final rank, and the
resulting square contains that replacement piece.

## Proof

Eliminate the promotion branch of pseudo-legality, then simplify the promotion
board update and the explicit `promotion_kinds` membership test.

:::

::: definition {#def-pseudo-legal}
title: Declarative pseudo-legal move relation
uses:
  - def-piece-geometry
  - def-castling-pseudo
  - def-en-passant-pseudo
  - def-promotion-pseudo
isabelle:
  theory: Chess_Pseudo_Legal
  fact: pseudo_legal_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Check side to move, source ownership, destination occupancy, geometry,
blocking, capture shape, initial pawn double advance, special-move conditions,
and castling path safety, but not ordinary post-move king safety.
:::

::: definition {#def-apply-move}
title: Total deterministic state transition
uses:
  - def-position
  - def-move
isabelle:
  theory: Chess_Transition
  fact: apply_move_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Update placement and captures, move the rook during castling, remove the
en-passant pawn, replace promoted pawns, revoke castling rights after king or
rook moves and original-rook captures, set or clear the en-passant target,
reset or increment the halfmove clock, increment the fullmove number after
Black's move, and toggle the turn.
:::

::: theorem {#thm-transition-fields}
title: Field-by-field transition equations
uses:
  - def-apply-move
isabelle:
  theory: Chess_Transition
  fact: apply_move_simps
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Publish stable simplification lemmas for every move constructor and every
position field, including castling-right and clock corner cases.

## Proof

Proceed by cases on the move constructor and relevant source/destination
squares, using record-update simplification and board extensionality.
:::

::: theorem {#thm-turn-alternation}
title: Every applied move alternates the side to move
uses:
  - def-apply-move
isabelle:
  theory: Chess_Transition
  fact: turn_apply_move
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For every move value, `turn (apply_move p m) = opponent (turn p)`.

## Proof

Unfold the common transition epilogue; the move-constructor-specific board
updates do not affect the turn field.

:::

## IV. Check, legality, and the verified move generator

::: definition {#def-check}
title: King square and check
uses:
  - def-position
  - def-piece-attacks
isabelle:
  theory: Chess_Check
  fact: in_check_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define a total optional king lookup and `in_check`.  Under the invariant, prove
the unique king-square characterization and equivalence with attack by the
opponent.
:::

::: definition {#def-legal-move}
title: Declarative legal-move semantics
uses:
  - def-pseudo-legal
  - def-apply-move
  - def-check
isabelle:
  theory: Chess_Legal
  fact: legal_move_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For ordinary moves, legality is pseudo-legality plus safety of the moving
side's king after the transition.  The castling branch additionally uses the
explicit source/transit/destination condition already exposed above.
:::

::: theorem {#thm-legal-king-safety}
title: A legal move leaves the moving side out of check
uses:
  - def-legal-move
isabelle:
  theory: Chess_Legal
  fact: legal_move_king_safe
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

If `legal_move p m`, then the colour that moved is not in check in
`apply_move p m`.

## Proof

Project the post-transition safety conjunct from legality; handle castling by
the dedicated three-square safety theorem.

:::

::: theorem {#thm-legal-preserves-invariant}
title: Legal moves preserve the proved core position invariant
uses:
  - def-legal-move
  - thm-transition-fields
  - thm-castling-safety
  - thm-en-passant-effect
  - thm-promotion-kind
isabelle:
  theory: Chess_Legal
  fact: legal_move_preserves_position_invariant
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

This is the first headline theorem.  It proves preservation of both king counts,
the absence of pawns on promotion ranks, castling-right consistency, and the
positive fullmove clock.  The transition removes rights from every touched
home square, so the theorem remains valid on malformed positions as well as
on reachable positions.

## Proof

Case-split on the move constructor and reuse the dedicated king-count lemmas
for ordinary, promotion, en-passant, and castling transitions.  The fullmove
clock follows directly from the transition equation.
:::

::: definition {#def-pseudo-moves}
title: Executable pseudo-legal move generator
uses:
  - def-move-universe
  - def-pseudo-legal
isabelle:
  theory: Chess_Move_Generator
  fact: pseudo_legal_moves_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Implement the executable reference generator as a filter over the complete
finite `candidate_moves` universe.  This deliberately favors a transparent
refinement proof over Stockfish-style performance; the resulting kernel is an
exhaustive correctness/reference generator, not an engine move generator.
:::

::: theorem {#thm-pseudo-moves-correct}
title: Pseudo-legal generator is sound and complete
uses:
  - def-pseudo-moves
  - thm-move-universe-complete
isabelle:
  theory: Chess_Move_Generator_Correct
  fact: pseudo_legal_moves_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Membership in the piece-directed pseudo-legal list is equivalent to the
declarative `pseudo_legal` predicate.

## Proof

Prove soundness by generator cases.  For completeness, place a declaratively
pseudo-legal move in the finite candidate universe and refine by its moving
piece and special-move constructor.

:::

::: definition {#def-legal-moves}
title: Executable legal-move filter over the finite reference generator
uses:
  - def-pseudo-moves
  - def-legal-move
isabelle:
  theory: Chess_Move_Generator
  fact: legal_moves_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Filter the exhaustive pseudo-legal list by the executable king-safety and
castling-safety tests, preserving its stable order.  The specification and
the finite candidate enumeration remain separate, so the filter is an
executable refinement rather than a definition of the declarative relation.

:::

::: theorem {#thm-legal-moves-sound}
title: Legal-move generator soundness
uses:
  - def-legal-moves
  - thm-pseudo-moves-correct
isabelle:
  theory: Chess_Move_Generator_Correct
  fact: legal_moves_sound
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Every member of `set (legal_moves p)` satisfies the declarative predicate
`legal_move p`.

## Proof

Eliminate list-filter membership, apply pseudo-generator soundness, and rewrite
the executable safety tests by their attack and check specifications.

:::

::: theorem {#thm-legal-moves-complete}
title: Legal-move generator completeness
uses:
  - def-legal-moves
  - thm-pseudo-moves-correct
isabelle:
  theory: Chess_Move_Generator_Correct
  fact: legal_moves_complete
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Every move satisfying `legal_move p` occurs in `set (legal_moves p)`.

## Proof

Use pseudo-generator completeness for the legality premise and show that the
post-move and castling safety conjuncts make the filter accept the move.

:::

::: theorem {#thm-legal-moves-correct}
title: Exact correspondence between executable and declarative legality
uses:
  - thm-legal-moves-sound
  - thm-legal-moves-complete
isabelle:
  theory: Chess_Move_Generator_Correct
  fact: legal_moves_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The central executable-correctness theorem is
`m \<in> set (legal_moves p) \<longleftrightarrow> legal_move p m`.
Also prove duplicate-freedom and determinism of generated order.  This is an
exact exhaustive reference-kernel result; no engine-grade complexity or
throughput claim is made.

## Proof

Combine soundness and completeness for the equivalence.  Lift distinctness
from the pseudo-generator through filtering; ordering follows from the fixed
square, piece, and move-constructor enumerations.
:::

## V. Histories, reachability, and outcomes

::: definition {#def-history}
title: Legal steps, valid histories, and reachability
uses:
  - def-legal-move
isabelle:
  theory: Chess_History
  fact: reachable_from_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define a labelled legal-step relation, replay of move lists, valid nonempty
position histories, and an explicit binary reflexive-transitive reachability
relation `reachable_from p q`; expose the initial-position abbreviation
`reachable q` as a derived predicate.  Preserve moves as labels so notation,
claims, and certificates can be checked against history.
:::

::: theorem {#thm-reachable-from-laws}
title: Binary reachability is reflexive, transitive, and step-closed
uses:
  - def-history
isabelle:
  theory: Chess_History
  fact: reachable_from_trans
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove the closure laws for arbitrary source and target positions and relate the
binary API to the initial-position predicate.  This keeps reachability useful
for subgames and semantic dead-position statements instead of baking in one
initial state.
:::

::: theorem {#thm-reachable-invariant}
title: Reachability preserves the proved core invariant
uses:
  - def-history
  - thm-initial-invariant
  - thm-legal-preserves-invariant
isabelle:
  theory: Chess_History
  fact: reachable_position_invariant
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Derive the package theorem by induction over the legal-step closure.  Every
reachable position satisfies the full proved structural `position_invariant`
(two king counts, pawn-rank condition, castling-right consistency, and positive
fullmove number).  The converse is intentionally not claimed: `legal_position`
remains the reachability predicate, while the invariant is only its preserved
structural safety layer.  The lower-level `reachable_initial_core_invariant`
fact remains available for the core clauses alone.

## Proof

Use reflexive-transitive-closure induction.  The base is the evaluated initial
placement; the step uses pseudo-legal king-count preservation and the positive
fullmove transition equation.
:::

::: definition {#def-mate-stalemate}
title: Checkmate and stalemate
uses:
  - def-check
  - def-legal-moves
isabelle:
  theory: Chess_Game
  fact: checkmate_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define checkmate and stalemate using check status plus absence of legal moves.
Prove executable characterizations and mutual exclusion on invariant positions.
:::

::: definition {#def-repetition-key}
title: Canonical position identity for repetition
uses:
  - def-legal-move
  - def-position
isabelle:
  theory: Chess_Repetition
  fact: repetition_key_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The key contains piece placement, side to move, castling possibilities, and an
effective en-passant component only when an en-passant capture is legally
available.  It excludes halfmove and fullmove counters.  State the exact
interpretation of FIDE 9.2.3 before proving equivalence properties.
:::

::: theorem {#thm-repetition-key-correct}
title: Repetition key exactly captures relevant move possibilities
uses:
  - def-repetition-key
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Repetition
  fact: same_repetition_position_iff
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Show that key equality gives equal placement, turn, castling and effective
en-passant possibilities; clocks are irrelevant.  Do not claim arbitrary key
equality implies equality of all future draw clocks.

## Proof

Expand record equality for the key and prove both directions componentwise.
For en passant, rewrite the effective component using legal-move correctness.
:::

::: definition {#def-repetition-rules}
title: Threefold claims and automatic fivefold repetition
uses:
  - def-history
  - def-repetition-key
isabelle:
  theory: Chess_Repetition
  fact: threefold_claimable_after_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Count occurrences in a valid history.  Model both a claim in the current
position and `threefold_claimable_after`, based on a declared legal move that
would create the third occurrence.  Keep automatic fivefold repetition
separate.
:::

::: theorem {#thm-clock-update}
title: Halfmove and fullmove clocks update exactly
uses:
  - thm-transition-fields
isabelle:
  theory: Chess_Draws
  fact: halfmove_clock_apply_move
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove reset after every pawn move or capture (including en passant and
promotion capture), increment after every other move, and fullmove increment
exactly after Black moves.

## Proof

Use move-constructor cases and the transition field equations.  Refine ordinary
moves by the source piece and destination occupancy to cover capture and pawn
branches exhaustively.
:::

::: definition {#def-move-count-draws}
title: Fifty-move claims and automatic seventy-five-move draws
uses:
  - def-history
  - thm-clock-update
isabelle:
  theory: Chess_Draws
  fact: fifty_move_claimable_after_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Represent both current-position and `fifty_move_claimable_after` declared-next-
move claims.  Define the
automatic seventy-five-move condition and its FIDE exception: checkmate by the
last move takes precedence.
:::

::: definition {#def-dead-position}
title: Semantic dead-position predicate
uses:
  - def-history
  - def-mate-stalemate
isabelle:
  theory: Chess_Draws
  fact: dead_position_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define a position as dead exactly when no continuation by any finite series of
legal moves can end in checkmate.  This is a semantic definition, not an
informal material heuristic.
:::

::: theorem {#thm-basic-dead-material}
title: King-only material cannot capture
uses:
  - def-dead-position
  - thm-legal-preserves-invariant
isabelle:
  theory: Chess_Draws
  fact: kings_only_material_no_capture
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove the executable kernel fact that a pseudo-legal move from a kings-only
material position is never a capture.  This is deliberately narrower than a
semantic dead-position classification; no informal K-v-K claim is hidden under
the theorem name.

## Proof

Unfold kings-only material, the destination restriction, and the capture-square
classifier for each move constructor.  The complete finite-square enumeration
supplies the material query at every candidate destination.
:::

::: definition {#def-game-result}
title: Terminal, automatic, and claimable game results
uses:
  - def-mate-stalemate
  - def-repetition-rules
  - def-move-count-draws
  - def-dead-position
isabelle:
  theory: Chess_Game
  fact: game_status_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Use a result datatype that distinguishes White win, Black win, automatic draw,
claimable draw, and ongoing play.  Encode checkmate priority and expose the
reason for a draw instead of erasing it.  The status function consumes a valid
history, not only its last position, because repetition is history-dependent.
:::

## VI. Interchange and notation

::: definition {#def-fen}
title: Total FEN printer and partial six-field parser
uses:
  - def-position
isabelle:
  theory: Chess_FEN_Text
  fact: parse_fen_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Parse and print placement, active colour, castling availability, en-passant
target, halfmove clock, and fullmove number.  Define a syntactic FEN invariant
separately from chess reachability and choose one documented canonical ordering
for castling flags.
:::

::: theorem {#thm-fen-roundtrip}
title: Generic six-field textual FEN roundtrip
uses:
  - def-fen
isabelle:
  theory: Chess_FEN_Text
  fact: parse_fen_print_fen_position
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove the generic textual placement parse/print round trip by induction over
the eight slash-separated ranks and the run-length encoder.  Prove the
turn, castling, en-passant, and arbitrary-length decimal clock codecs, then
compose them with the six-field splitter.  The resulting parser recovers the
printed text for every position whose fullmove number is positive.  This is a
parse-after-print canonicalization theorem, not a converse for arbitrary
non-canonical input; the canonical initial serialization remains an executable
regression.

## Proof

The placement theorem covers compressed ranks and board extensionality.  The
field theorems cover active colour, canonical castling order, en-passant
coordinates, and arbitrary-length decimal clocks.  The final composition
also discharges the parser's required positive-fullmove guard.
:::

::: definition {#def-uci}
title: UCI-style coordinate move notation
uses:
  - def-move
isabelle:
  theory: Chess_Notation
  fact: parse_uci_text_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Support the typed UCI datatype and its canonical lowercase textual
source/destination strings with promotion suffixes.  Resolve castling and en
passant in position context so notation does not need special wire
constructors; the textual parser is executable and exported with the kernel.
:::

::: theorem {#thm-uci-roundtrip}
title: UCI parsing and printing round trip on legal moves
uses:
  - def-uci
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Notation
  fact: parse_print_uci_legal_move_unique
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The legal UCI representation is injective, including the exceptional move
constructors, so parsing canonical textual coordinate notation in the source
position returns exactly the printed legal move without a uniqueness
assumption at the call site.

## Proof

First prove the raw textual codec round trip, then prove UCI injectivity by
constructor cases and resolve the legal internal constructor by generator
correctness.

:::

::: theorem {#thm-uci-text-codec}
title: Canonical textual UCI codec round trip
uses:
  - def-uci
isabelle:
  theory: Chess_Notation
  fact: parse_uci_text_raw_uci_text
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The raw parser accepts exactly four-character coordinate moves or five-character
lowercase promotion moves and is inverse to the canonical printer for every
typed UCI move.
:::

::: definition {#def-san}
title: Context-sensitive Standard Algebraic Notation
uses:
  - def-mate-stalemate
  - thm-legal-moves-correct
isabelle:
  theory: Chess_SAN
  fact: print_san_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Implement Appendix C piece letters, pawn notation, captures, minimal legal-move
disambiguation, promotion, O-O/O-O-O, check, and mate suffixes.  Parsing is
position-dependent and returns a move only when the notation denotes exactly
one legal move.  Treat optional annotations and locale-specific piece letters
as out of scope.
:::

::: theorem {#thm-san-roundtrip}
title: Canonical SAN round trip under legal-list uniqueness
uses:
  - def-san
isabelle:
  theory: Chess_SAN
  fact: parse_print_san_legal_move_checked
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove printing then parsing returns the original legal move under the
decidable finite-list predicate `san_unique_on_legal_moves`.  A proved iff
relates that predicate to injectivity of the SAN printer on the legal move
list, making the arbitrary-FEN caveat explicit.

## Proof

The parser theorem consumes the finite-list uniqueness predicate.  The printer
implements minimal disambiguation, while check and mate suffixes are defined
from the post-transition outcome definitions.  The executable regression
discharges the predicate for both the initial position and Kiwipete, and
checks the resulting legal-list round trips for both positions.
:::

::: theorem {#thm-san-global-roundtrip}
title: Unconditional SAN injectivity and parse-after-print for legal moves
uses:
  - def-san
  - thm-san-normal-decomposition
isabelle:
  theory: Chess_SAN
  fact: parse_print_san_legal_move_unconditional
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove that the canonical SAN printer is injective on every pair of legal moves,
including pawn, promotion, en-passant, and castling constructors, and derive
the parser/printing round trip without a finite-list uniqueness premise.  The
finite-list predicate above remains an executable regression certificate, but
it is no longer a semantic precondition for legal SAN parsing.

## Proof

Strip the check/mate suffix, split castle versus non-castle constructors, and
use the constructor-level geometry and collision lemmas in
`san_noncastle_noncastle_injective` together with the castling cases.
The parser theorem then applies `parse_print_san_legal_move` with the global
injectivity fact.
:::

::: theorem {#thm-san-structural-injectivity}
title: SAN destination and minimal-disambiguation injectivity
uses:
  - def-san
isabelle:
  theory: Chess_SAN
  fact: san_destination_text_injective
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove the position-independent destination-field encoding is injective, and
prove that, for two non-pawn legal source pieces with nonempty competitor
sets, equal minimal disambiguation text determines the source square.  The
proof makes the exact hypotheses visible: the competitor relation supplies
the file/rank conflict facts, while the finite file/rank character coding
separates the one- and two-character cases.  These lemmas feed the global
legal-move printer injectivity theorem; the finite-list predicate above remains
an executable regression certificate rather than a semantic precondition.
:::

::: theorem {#thm-san-disambiguation-source}
title: Minimal SAN disambiguation recovers the source square
uses:
  - thm-san-structural-injectivity
isabelle:
  theory: Chess_SAN
  fact: san_disambiguation_source_eq
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The source-recovery theorem is stated against the actual legal competitor
relation and records the non-pawn and nonempty-competitor hypotheses explicitly.
It is the structural bridge used when auditing SAN collisions and is consumed
by the global legal-move injectivity proof.
:::

::: theorem {#thm-san-normal-decomposition}
title: Non-pawn normal SAN decomposition and injectivity
uses:
  - thm-san-disambiguation-source
isabelle:
  theory: Chess_SAN
  fact: san_normal_nonpawn_injective
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For two legal normal moves whose source pieces are the same non-pawn kind,
equal non-castling SAN text first recovers the destination, capture marker,
and disambiguation text, then uses the legal competitor relation to recover
the source and hence the whole move.  The complete global theorem additionally
handles pawn geometry, promotion, en passant, and castling collisions.
:::

## VII. Forced mate and proof certificates

::: definition {#def-forced-mate}
title: Declarative bounded-ply forced-mate semantics
uses:
  - def-game-result
  - def-legal-move
isabelle:
  theory: Chess_Mate
  fact: forced_mate_within_history_recurrence
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define mate within at most `n` plies for a fixed attacker from a history,
extending that history at every recursive step.  At attacker nodes there must
exist a legal continuation; at defender nodes every legal reply must retain the
bound.  Checkmate of the defender succeeds, while stalemate, dead positions,
automatic draws, and checkmate of the attacker fail.  Optional FIDE claims are
defender actions: a claim available in the current position fails the
defender node, and a legal announced move that creates a threefold or
fifty-move claim is excluded as a drawing reply; the attacker may decline its
own claim.  State an exact-ply variant separately.  Also provide a deliberately
scoped puzzle predicate on a bare position that ignores repetition claims when
no prior history is supplied.
:::

::: definition {#def-mate-checker}
title: Executable bounded mate checker
uses:
  - def-forced-mate
  - def-legal-moves
isabelle:
  theory: Chess_Mate
  fact: forced_mate_within_policy.simps(1)
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Compute the bounded alternating game tree from a history using `legal_moves`,
short-circuiting existential attacker nodes and checking every defender reply
while extending the history used by terminal-draw checks.  The checker is
parameterized by three policies: an automatic terminal predicate, a current
defender-claim predicate, and an intended-move defender-claim predicate.  The
semantic specialization supplies exact dead-position reachability and the
FIDE claim predicates; the executable specialization leaves the automatic
terminal predicate explicit while retaining the same claim policy.

:::

::: theorem {#thm-mate-checker-correct}
title: Executable mate checker equals declarative forced mate
uses:
  - def-mate-checker
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Mate
  fact: forced_mate_within_history_refinement
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Prove the history-threaded recursion equations and the semantic/parameterized
specializations by induction on the ply bound.  The refinement identifies the
public history-aware predicate with the policy checker, including automatic
terminals, current defender claims, and announced claim-producing replies.
The theorem must account for empty move lists and every terminal game status
explicitly.

## Proof

Induct on the bound and split on whose turn it is.  Rewrite existential list
search and universal list checking with legal-move generator correctness, then
handle terminal statuses before the recursive case.
:::

::: definition {#def-mate-certificate}
title: Finite attacker/defender mate-tree certificates
uses:
  - def-forced-mate
isabelle:
  theory: Chess_Certificates
  fact: check_mate_certificate_policy.simps(1)
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

An attacker node records one chosen legal move; a defender node records one
subcertificate for every legal reply.  The history-aware policy checker
rejects stalemate and automatic terminals before descending, rejects a current
defender claim, and rejects every listed reply that would create an intended
threefold or fifty-move claim.  The claimed ply budget and terminal evidence
are checked by the kernel rather than being trusted parser metadata.  The
legacy position-only checker remains as a compatibility layer.
:::

::: theorem {#thm-mate-certificate-sound}
title: Accepted mate certificates imply forced mate
uses:
  - def-mate-certificate
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Certificates
  fact: check_mate_certificate_history_sound
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

If the history-aware policy certificate checker accepts a certificate for
history `hs`, attacker `c`, and budget `n`, then
`forced_mate_within_history c hs n` holds.  This includes the defender's
current and intended-move claim policy.  The legacy position certificate
soundness theorem remains available for compatibility with the original
position-only showcase.

## Proof

Induct on the certificate and budget.  Attacker nodes provide the existential
witness; defender nodes use reply-list coverage plus legal-move completeness,
and carry the claim exclusions into every appended child history.

:::

::: theorem {#thm-mate-certificate-complete}
title: Every bounded forced mate has a finite certificate
uses:
  - def-mate-certificate
  - thm-mate-checker-correct
isabelle:
  theory: Chess_Certificates
  fact: forced_mate_history_has_certificate
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The entry constructs a finite history-aware policy certificate at every
forced-mate bound.  Attacker nodes choose a recursively certified move;
defender nodes enumerate every legal reply that is not a claim-producing
announced move and attach its recursively certified subcertificate.  Thus the
certificate relation is complete for the same semantics used by the public
mate search.

## Proof

Induct on the bound.  The terminal case chooses MateTerminal; attacker nodes
use the existential witness and defender nodes use the finite legal-move list
with a choice function for each recursively certified, non-claim-producing
reply.
:::

## VIII. Validation, symmetry, and executable delivery

::: definition {#def-perft}
title: Perft leaf-count function
uses:
  - def-legal-moves
  - def-apply-move
isabelle:
  theory: Chess_Perft
  fact: perft_zero
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Define depth-zero as one leaf and each successor depth as the sum over all
generated legal continuations.  Also expose per-move divide counts for
diagnosing generator errors.
:::

::: theorem {#thm-initial-legal-facts}
title: Initial position has exactly twenty legal moves and neither king in check
uses:
  - def-initial-position
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Examples
  fact: initial_position_legal_moves_20
  session: Chess
status:
  blueprint: reviewed
  formal: tainted
  agent: ready

Also prove that the initial position is neither checkmate nor stalemate and,
if maintainable, identify the exact set of sixteen pawn advances and four
knight moves.

## Proof

Evaluate the piece-directed generator on the initial board, normalize the
finite list, and use generator correctness to transfer the computation to the
declarative claims.
:::

::: theorem {#thm-initial-perft}
title: Verified standard initial-position perft counts
uses:
  - def-perft
  - thm-initial-legal-facts
isabelle:
  theory: Chess_Perft
  fact: initial_position_perft_all
  session: Chess
status:
  blueprint: reviewed
  formal: tainted
  agent: ready

Prove by kernel-checked evaluation perft 1 = 20, perft 2 = 400,
perft 3 = 8902, and perft 4 = 197281, collected in one named regression
conjunction as well as the individual depth facts.

## Proof

Unfold `perft` to the requested fixed depth and certify the normalized numeral
with Isabelle evaluation.  Keep the theorem dependent on the verified
generator rather than importing an external count certificate.
:::

::: definition {#def-symmetry}
title: Board reflection with colour and turn inversion
uses:
  - def-position
  - def-move
isabelle:
  theory: Chess_Symmetry
  fact: mirror_position_def
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Mirror ranks, swap colours, transform pieces, castling rights, en-passant
targets, moves, and histories.  Prove the transformations are involutions.
:::

::: theorem {#thm-symmetry-legality}
title: Reflected attack geometry, check, and pseudo-legal constructors
uses:
  - def-symmetry
  - thm-legal-moves-correct
  - def-game-result
isabelle:
  theory: Chess_Symmetry
  fact: in_check_mirror_unique
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The verified symmetry layer proves rank, square, piece, board, castling-right,
position, and move involutions, together with file/rank/diagonal, ordinary
piece-geometry, between/ray-clear, slider, piece-attack, attacked-square,
pseudo-legal constructor, and check transport.  The check theorem is
explicitly parameterized by existence and uniqueness of the relevant king.
The fullmove clock is deliberately not included in the board/legality
symmetry because its conventional increment is tied to the unreflected
black-move numbering; legality itself is handled by the separate theorem
below.

## Proof

The involutions are constructor/extensionality proofs.  Geometry and attack
transport use reflected rank-index arithmetic, the involutive square map, and
color-swapped pawn directions; ray-clear transport uses the mapped middle
square predicate.
:::

::: theorem {#thm-symmetry-pseudo-legal}
title: Pseudo-legal move reflection, including special constructors
uses:
  - def-symmetry
  - def-pseudo-legal
isabelle:
  theory: Chess_Symmetry
  fact: pseudo_legal_mirror
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For every move constructor, including ordinary moves, promotion, en passant,
and all four castling choices, reflection with colour and turn inversion
preserves the declarative pseudo-legal relation.  The proof separately
transports slider clearance, pawn direction, castling path safety, and the
history-independent special-move prerequisites.
:::

::: theorem {#thm-symmetry-legal}
title: Legal-move, checkmate, and stalemate reflection
uses:
  - def-symmetry
  - def-legal-move
  - thm-legal-preserves-invariant
  - thm-symmetry-pseudo-legal
isabelle:
  theory: Chess_Symmetry
  fact: legal_move_mirror
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Under the core position invariant, reflecting the board, colours, turn, and
move constructor preserves the declarative legal-move relation.  The proof
transports the complete board transition (including castling, en passant,
and promotion), the king-safety guard, and castling transit safety.  The same
invariant then yields checkmate_mirror and stalemate_mirror; the fullmove
number metadata is intentionally kept outside this semantic equivalence.
:::

::: theorem {#thm-symmetry-checkmate}
title: Checkmate reflection
uses:
  - thm-symmetry-legal
  - def-game-result
isabelle:
  theory: Chess_Symmetry
  fact: checkmate_mirror
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For invariant positions, reflection preserves the conjunction of being in
check and having no legal move.
:::

::: theorem {#thm-symmetry-stalemate}
title: Stalemate reflection
uses:
  - thm-symmetry-legal
  - def-game-result
isabelle:
  theory: Chess_Symmetry
  fact: stalemate_mirror
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

For invariant positions, reflection preserves the conjunction of being out
of check and having no legal move.
:::

::: theorem {#thm-regression-examples}
title: Certified tactical and rules-edge examples
uses:
  - thm-fen-roundtrip
  - thm-mate-checker-correct
  - thm-mate-certificate-sound
  - thm-mate-certificate-complete
  - thm-san-roundtrip
  - thm-san-global-roundtrip
isabelle:
  theory: Chess_Examples
  fact: example_suite_correct
  session: Chess
status:
  blueprint: reviewed
  formal: tainted
  agent: ready

The executable suite includes initial-position, Kiwipete, and the
en-passant/promotion-rich standard perft position legal-move/perft/FEN/SAN facts,
named castling, en-passant, promotion, mate-in-one, stalemate, castling-through-
check, en-passant discovered-check, promotion-mate, SAN-disambiguation,
fivefold-repetition, and fifty/seventy-five-move clock cases.  The suite also
checks SAN uniqueness and a legal SAN parse/print round trip for both the
initial and Kiwipete positions, a history-aware mate certificate for the
mate-in-one fixture, and the Kiwipete counts 48, 2039, 97862 together with
the standard second-position counts 14, 191, 2812.
Each example is a theorem or checked evaluation, not an external unit test
alone.

## Proof

Parse each canonical FEN, evaluate the relevant verified decision procedure,
and close the resulting finite proposition by normalization.  Keep each case
as a named theorem so failures identify a single rule boundary.
:::

::: theorem {#thm-mate-two-showcase}
title: Kernel-checked history-aware three-ply certificate for a two-move mate
uses:
  - def-mate-certificate
  - thm-mate-certificate-sound
  - thm-legal-moves-correct
isabelle:
  theory: Chess_Mate_Two
  fact: mate_two_candidate_history_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

The Chess_Mate_Two theory instantiates the history-aware, claim-aware
certificate checker on the FEN
kr6/1r1N4/2Q5/8/8/8/8/K7 w - - 0 1. It proves a White key move
Nd7-c5, exhausts the seven legal Black replies, and certifies the
corresponding mate continuations. The checker counts plies: the headline
theorem is therefore a three-ply certificate (White move, Black reply, White
mate), which is the conventional two-move mate-in-two. The finite
position-specific facts are evaluated by Isabelle's kernel evaluator. The
theorem mate_two_candidate_history_correct derives
forced_mate_within_history through check_mate_certificate_history_sound, so
optional defender threefold and fifty-move claims are explicitly excluded at
every defender node. The older position-only theorem remains as a
compatibility result, not as the headline claim.

## Proof
Prove legality, draw-status, non-dead-position, repetition-key, and terminal
checkmate facts for each finite branch; use
check_mate_certificate_history_sound for the headline theorem and retain the
legacy soundness theorem only for compatibility. Keep the ply convention
explicit so the example cannot be mistaken for a two-ply bound.
:::

::: theorem {#thm-executable-kernel}
title: Exportable verified chess kernel
uses:
  - thm-legal-moves-correct
  - thm-legal-preserves-invariant
  - thm-reachable-invariant
  - thm-fen-roundtrip
  - thm-uci-roundtrip
  - thm-san-roundtrip
  - thm-san-global-roundtrip
  - thm-mate-certificate-sound
  - thm-mate-certificate-complete
  - thm-mate-checker-correct
  - thm-symmetry-legal
  - thm-symmetry-checkmate
  - thm-symmetry-stalemate
  - def-perft
isabelle:
  theory: Chess
  fact: chess_kernel_correct
  session: Chess
status:
  blueprint: reviewed
  formal: proved
  agent: ready

Collect the headline theorem inventory: exact legal-generator refinement,
structural-invariant preservation and reachability lifting, typed/textual FEN,
UCI and unconditional SAN round trips, history-aware certificate
soundness/completeness, mate-policy refinement, perft, and legal/checkmate/
stalemate symmetry transport.  Export parse_fen, print_fen, legal move
generation, apply_move, checkmate/stalemate predicates, typed and textual UCI
parsing/printing, canonical SAN parsing/printing, the terminal/claim-policy-
parameterized bounded checker, and perft to SML.  The exact semantic
dead-position specialization and certificate relations remain kernel-checked
logical specifications; the unbounded reachability branch is intentionally not
presented as an executable decision procedure.  Generated code is a consumer
of proved equations; code generation is not part of the logical trusted base.

## Proof

Assemble the previously proved refinement, invariant, reachability, parser,
notation, mate, certificate, symmetry, and perft theorems into a named
conjunction, then invoke `export_code` only after the logical theorem is
closed.
:::

## Theory and delivery plan

The intended top-level AFP theories are:

```text
Chess_Square                 Chess_Board
Chess_Position               Chess_Geometry
Chess_Attacks                Chess_Move
Chess_Castling               Chess_En_Passant
Chess_Promotion              Chess_Pseudo_Legal
Chess_Transition             Chess_Check
Chess_Legal                  Chess_Move_Generator
Chess_Move_Generator_Correct Chess_History
Chess_Repetition             Chess_Draws
Chess_Game                   Chess_FEN               Chess_FEN_Text
Chess_Notation               Chess_SAN
Chess_Mate                   Chess_Certificates
Chess_Perft                  Chess_Symmetry
Chess_Examples               Chess_Mate_Two
Chess
```

Implementation should proceed in eight gates matching the sections above.
The first AFP-quality release gate is reached only when both headline theorems
`legal_moves_correct` and the proved core-invariant preservation theorem are
proved,
the full document build passes, and special-move regression examples pass.
Notation, draw claims, mate certificates, symmetry, and perft are part of this
full Blueprint rather than silently deferred, but their isolated theories keep
the verified move kernel reviewable throughout development.

Before AFP packaging, perform a current upstream and AFP reuse audit, cite the
FIDE rules and notation/interchange specifications in `document/root.bib`, run
the repository build and audit tools, run a targeted Sledgehammer pass only on
touched proof ranges, and stage only AFP source.  No generated Blueprint site,
task pack, exported executable, perft cache, or test artifact belongs in the
submission archive.
