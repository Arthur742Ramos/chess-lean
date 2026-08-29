import Chess.Examples
import Chess.MateTwo

/-!
# Public correctness bundle

The registry-facing proof development has one executable kernel and a small
set of independently checked regression facts.  This theorem collects the
main interfaces without replacing their individual declarations: legal move
generation is extensionally correct, the Boolean and proposition-level
legality predicates agree, typed FEN is lossless, standard perft positions
match their reference counts, notation round-trips on the initial move, and
the Isabelle mate-in-two certificate is accepted by both certificate layers.
It also records the rule-level adequacy witness for bounded forced mate.
-/

namespace Chess

def kernelClaim : Prop :=
  (∀ p m, m ∈ legalMoves p ↔ legalMove p m) ∧
  (∀ p m, legalMove p m ↔ legalMoveB p m = true) ∧
  (∀ p, parseFenFields (printFenFields p) = some p) ∧
  (legalMoves initialPosition).length = 20 ∧
  perft initialPosition 1 = 20 ∧
  perft initialPosition 2 = 400 ∧
  perft initialPosition 3 = 8902 ∧
  printFen initialPosition =
    "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1" ∧
  perft kiwipetePosition 1 = 48 ∧
  perft kiwipetePosition 2 = 2039 ∧
  perft perftPositionThree 1 = 14 ∧
  perft perftPositionThree 2 = 191 ∧
  perft perftPositionThree 3 = 2812 ∧
  (printSan initialPosition
      (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩)) = "e4") ∧
  (parseSanMove initialPosition "e4" =
      some (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩))) ∧
  sanUniqueOnLegalMoves initialPosition ∧
  (parseUciText initialPosition "e2e4" =
      some (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩))) ∧
  legalMoveB castleExample .whiteKingCastle = true ∧
  (legalMoveB enPassantExample
      (.enPassant (⟨4, by decide⟩, ⟨4, by decide⟩)
        (⟨3, by decide⟩, ⟨5, by decide⟩)) = true) ∧
  ((applyMove enPassantExample
      (.enPassant (⟨4, by decide⟩, ⟨4, by decide⟩)
        (⟨3, by decide⟩, ⟨5, by decide⟩))).board
      (⟨3, by decide⟩, ⟨4, by decide⟩) = none) ∧
  (legalMoveB promotionExample
      (.promotion (⟨0, by decide⟩, ⟨6, by decide⟩)
        (⟨0, by decide⟩, ⟨7, by decide⟩) .queen) = true) ∧
  ((applyMove promotionExample
      (.promotion (⟨0, by decide⟩, ⟨6, by decide⟩)
        (⟨0, by decide⟩, ⟨7, by decide⟩) .queen)).board
      (⟨0, by decide⟩, ⟨7, by decide⟩) = some ⟨.white, .queen⟩) ∧
  (∀ p, mirrorPosition (mirrorPosition p) = p) ∧
  (checkMateCertificateB .white mateTwoCandidate 3 mateTwoCertificate = true) ∧
  (checkMateCertificateExecutable .white [mateTwoCandidate] 3 mateTwoCertificate = true) ∧
  (ruleCertificateCheckB (fun _ => false) .white mateTwoCandidate 3
    mateTwoCertificate = true) ∧
  ruleForcedMate (fun _ => false) .white mateTwoCandidate 3

theorem kernel_correct : kernelClaim := by
  constructor
  · intro p m
    exact legalMoves_correct p m
  constructor
  · intro p m
    exact legalMove_iff_legalMoveB p m
  constructor
  · intro p
    exact parseFenFields_printFenFields p
  constructor
  · exact initialPosition_legal_moves_20
  constructor
  · exact initialPosition_perft_1
  constructor
  · exact initialPosition_perft_2
  constructor
  · exact initialPosition_perft_3
  constructor
  · exact initialPosition_fen
  constructor
  · exact kiwipete_perft_1
  constructor
  · exact kiwipete_perft_2
  constructor
  · exact perftPositionThree_perft_1
  constructor
  · exact perftPositionThree_perft_2
  constructor
  · exact perftPositionThree_perft_3
  constructor
  · exact san_initial_e2e4
  constructor
  · exact san_initial_e2e4_parse
  constructor
  · exact san_initial_unique
  constructor
  · exact parseUciText_printUciText_initial_e2e4
  constructor
  · exact castleExample_legal
  constructor
  · exact enPassantExample_legal
  constructor
  · exact enPassantExample_captured
  constructor
  · exact promotionExample_legal
  constructor
  · exact promotionExample_destination
  constructor
  · intro p
    exact mirrorPosition_involutive p
  constructor
  · exact mateTwoCertificate_checked
  constructor
  · exact mateTwoCertificate_history_checked
  constructor
  · exact mateTwoCertificate_rules_checked
  · exact mateTwoCertificate_rules_forced

end Chess
