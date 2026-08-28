import Chess.Symmetry
import Chess.FENText

/-!
# Executable regression positions

These are the concrete checks carried by the Isabelle entry: the initial
position, Kiwipete, the standard third perft position, and isolated castling,
en-passant, and promotion states. They are intentionally theorem statements,
so CI checks the same values with Lean's native evaluator.
-/

namespace Chess

def kiwipetePosition : Position :=
  Option.getD
    (parseFen "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1")
    initialPosition

def perftPositionThree : Position :=
  Option.getD
    (parseFen "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1")
    initialPosition

def castleExample : Position :=
  { board := fun s =>
      if s = (⟨4, by decide⟩, ⟨0, by decide⟩) then some ⟨.white, .king⟩
      else if s = (⟨7, by decide⟩, ⟨0, by decide⟩) then some ⟨.white, .rook⟩
      else if s = (⟨4, by decide⟩, ⟨7, by decide⟩) then some ⟨.black, .king⟩
      else none
    turn := .white
    castling := {.whiteKingSide}
    enPassant := none
    halfmove := 0
    fullmove := 1 }

def enPassantExample : Position :=
  { board := fun s =>
      if s = (⟨4, by decide⟩, ⟨0, by decide⟩) then some ⟨.white, .king⟩
      else if s = (⟨4, by decide⟩, ⟨4, by decide⟩) then some ⟨.white, .pawn⟩
      else if s = (⟨3, by decide⟩, ⟨4, by decide⟩) then some ⟨.black, .pawn⟩
      else if s = (⟨4, by decide⟩, ⟨7, by decide⟩) then some ⟨.black, .king⟩
      else none
    turn := .white
    castling := ∅
    enPassant := some (⟨3, by decide⟩, ⟨5, by decide⟩)
    halfmove := 0
    fullmove := 2 }

def promotionExample : Position :=
  { board := fun s =>
      if s = (⟨4, by decide⟩, ⟨0, by decide⟩) then some ⟨.white, .king⟩
      else if s = (⟨0, by decide⟩, ⟨6, by decide⟩) then some ⟨.white, .pawn⟩
      else if s = (⟨4, by decide⟩, ⟨7, by decide⟩) then some ⟨.black, .king⟩
      else none
    turn := .white
    castling := ∅
    enPassant := none
    halfmove := 0
    fullmove := 1 }

theorem initialPosition_legal_moves_20 :
    (legalMoves initialPosition).length = 20 := by
  native_decide

theorem initialPosition_not_in_check :
    inCheckB initialPosition .white = false ∧
      inCheckB initialPosition .black = false := by
  native_decide

theorem initialPosition_not_terminal :
    checkmateB initialPosition = false ∧ stalemateB initialPosition = false := by
  native_decide

theorem initialPosition_perft_1 : perft initialPosition 1 = 20 := by
  native_decide

theorem initialPosition_perft_2 : perft initialPosition 2 = 400 := by
  native_decide

theorem initialPosition_perft_3 : perft initialPosition 3 = 8902 := by
  native_decide

theorem initialPosition_fen :
    printFen initialPosition =
      "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1" := by
  native_decide

theorem initialPosition_fen_parses :
    (parseFen (printFen initialPosition)).isSome = true := by
  native_decide

theorem kiwipete_perft_1 : perft kiwipetePosition 1 = 48 := by
  native_decide

theorem kiwipete_perft_2 : perft kiwipetePosition 2 = 2039 := by
  native_decide

theorem perftPositionThree_perft_1 : perft perftPositionThree 1 = 14 := by
  native_decide

theorem perftPositionThree_perft_2 : perft perftPositionThree 2 = 191 := by
  native_decide

theorem perftPositionThree_perft_3 : perft perftPositionThree 3 = 2812 := by
  native_decide

theorem castleExample_legal :
    legalMoveB castleExample .whiteKingCastle = true := by
  native_decide

theorem castleExample_destination :
    (applyMove castleExample .whiteKingCastle).board
      (⟨6, by decide⟩, ⟨0, by decide⟩) = some ⟨.white, .king⟩ := by
  native_decide

theorem enPassantExample_legal :
    legalMoveB enPassantExample
      (.enPassant (⟨4, by decide⟩, ⟨4, by decide⟩)
        (⟨3, by decide⟩, ⟨5, by decide⟩)) = true := by
  native_decide

theorem enPassantExample_captured :
    (applyMove enPassantExample
      (.enPassant (⟨4, by decide⟩, ⟨4, by decide⟩)
        (⟨3, by decide⟩, ⟨5, by decide⟩))).board
      (⟨3, by decide⟩, ⟨4, by decide⟩) = none := by
  native_decide

theorem promotionExample_legal :
    legalMoveB promotionExample
      (.promotion (⟨0, by decide⟩, ⟨6, by decide⟩)
        (⟨0, by decide⟩, ⟨7, by decide⟩) .queen) = true := by
  native_decide

theorem promotionExample_destination :
    (applyMove promotionExample
      (.promotion (⟨0, by decide⟩, ⟨6, by decide⟩)
        (⟨0, by decide⟩, ⟨7, by decide⟩) .queen)).board
      (⟨0, by decide⟩, ⟨7, by decide⟩) = some ⟨.white, .queen⟩ := by
  native_decide

theorem mirror_initial_position_legal_moves_20 :
    (legalMoves (mirrorPosition initialPosition)).length = 20 := by
  native_decide

end Chess
