# Chess in Isabelle/HOL

This AFP-style entry formalizes an executable semantics for orthodox chess.
The kernel covers finite board coordinates, attacks, special moves, total
state transitions, check, declarative legality, and an exhaustive verified
finite reference generator, histories, repetition and clock predicates, textual and typed
six-field FEN, typed and canonical textual UCI plus SAN move resolution,
intended-move draw claims, bounded forced mate, recursively
checked certificate soundness, arbitrary-depth certificate completeness,
reflection involutions with attack/ray, pseudo-legal and legal-move transport,
unique-king check transport, checkmate/stalemate reflection, perft, and
executable regression facts.  The top-level kernel exports FEN, legal moves,
state application, checkmate/stalemate, typed and textual UCI parsing/printing,
SAN parsing/printing, the history-threaded policy-parameterized mate checker,
and perft to SML; this is a correctness/reference kernel rather than a
Stockfish-style efficient engine generator.  The exact semantic dead-position
specialization and mate certificates remain logical checked artifacts: the
semantic mate policy includes the unbounded reflexive-transitive
`dead_position` predicate, while generated mate code takes a terminal policy
as an explicit parameter.  The executable regression suite includes
the standard Kiwipete counts 48, 2039, and 97862, plus the standard
en-passant/promotion-rich position counts 14, 191, and 2812, in addition to
the initial-position counts.  The public mate policy treats optional
threefold and fifty-move claims as defender drawing actions: current claims
fail the search on defender turns, while announced legal claim-producing moves
are rejected as defensive replies.  The attacker may decline an optional claim.
UCI injectivity is proved for legal moves, giving an unconditional UCI
round-trip theorem.  SAN now proves unconditional injectivity of the canonical
printer on every pair of legal moves and the corresponding parse-after-print
theorem.  The finite-list `san_unique_on_legal_moves` predicate and its
injectivity characterization remain as executable regression certificates for
concrete positions; the initial position and Kiwipete both discharge it by
kernel evaluation.  The structural proof covers destination encoding, capture
markers, minimal disambiguation, pawn geometry, promotion, en passant, and
castling, so arbitrary legal FEN positions no longer rely on a finite-list
uniqueness premise.  In particular, for legal normal moves with non-pawn
sources, equal non-castling SAN text is decomposed into destination, capture,
disambiguation, and source equality.

The capstone theorem `chess_kernel_correct` now inventories these results
together: exhaustive generator correctness, invariant preservation and
reachability lifting, typed/textual FEN and UCI round trips, unconditional SAN
injectivity/round trip, history-aware certificate soundness/completeness,
mate-policy refinement, perft, and legal/checkmate/stalemate symmetry.  The
exported SML module is therefore accompanied by a theorem inventory that
reflects the full development rather than only a small regression conjunction.

The rules baseline is the FIDE Laws of Chess effective 1 January 2023. The
logical development deliberately separates the proved core position invariant
from full game legality: `position_invariant` is the structural safety layer
(king counts, pawn-rank safety, castling-right consistency, and positive
fullmove number), while `legal_position` is defined as reachability from the
initial position.  Every reachable position is proved to satisfy the structural
invariant, but the invariant is not presented as a characterization of
reachability.  Claimable and automatic draws remain distinct.  The
textual placement and all six FEN fields have a parse-after-print round trip
for positions with positive fullmove numbers.  This is a canonicalization
statement, not a converse for arbitrary non-canonical input.  The canonical
initial position is also checked as an executable regression.
The core preservation theorem covers king counts, pawn-rank safety,
castling-right consistency, and fullmove positivity; rights are removed
conservatively from all move-touched home squares.
The symmetry layer transports all pseudo-legal constructors, including
castling, en passant, and promotion, and proves legal-move equivalence plus
checkmate/stalemate reflection under the stated position invariant.  The
fullmove clock is intentionally kept as a separate metadata field: its
black-move numbering convention is not silently conflated with the
board/legality symmetry.

The separate Chess_Mate_Two theory provides a kernel-checked certificate for a
concrete two-move mate.  Its legacy position-only forced_mate_within bound is
measured in plies, so
the certified line is three plies (White key move, Black reply, White mate).
The certificate exhausts the seven legal Black replies and records the
terminal checkmates; the finite branch facts are evaluated by Isabelle while
the history-aware certificate checker and its soundness/completeness theorems
connect certificates to the public policy semantics.  In particular,
mate_two_history_certificate_checked and mate_two_candidate_history_correct
check the same showcase against the history-threaded, claim-aware semantics;
the older position-only theorem is retained only as a compatibility result.

Proof-only build:

    isabelle build -D . -o document=false Chess

The final AFP-style build also checks the generated document:

    isabelle build -D . Chess

AI assistance was used for proof engineering. The final definitions,
statements, and proofs are checked by Isabelle.
