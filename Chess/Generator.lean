import Chess.Legality

/-!
# Finite move universe and verified filtering

The candidate list is intentionally transparent: every pair of board squares,
every promotion kind, both en-passant endpoints, and all four castling moves
are included. Legal moves are a filter of this universe, and the main theorem
below proves that the filter is extensionally equal to the declarative
relation.
-/

namespace Chess

def squarePairs : List (Square × Square) :=
  allSquares.flatMap (fun s => allSquares.map (fun t => (s, t)))

def ordinaryCandidates : List Move :=
  squarePairs.map (fun st => .normal st.1 st.2)

def promotionCandidates : List Move :=
  squarePairs.flatMap (fun st => allPromotionKinds.map (fun k => .promotion st.1 st.2 k))

def enPassantCandidates : List Move :=
  squarePairs.map (fun st => .enPassant st.1 st.2)

def castleCandidates : List Move :=
  [.whiteKingCastle, .whiteQueenCastle, .blackKingCastle, .blackQueenCastle]

def candidateMoves : List Move :=
  ordinaryCandidates ++ promotionCandidates ++ enPassantCandidates ++ castleCandidates

def legalMoves (p : Position) : List Move :=
  candidateMoves.filter (fun m =>
    @decide (legalMove p m) (legalMoveDecidable p m))

theorem normal_mem_candidateMoves (s t : Square) :
    .normal s t ∈ candidateMoves := by
  simp [candidateMoves, ordinaryCandidates, squarePairs]

theorem promotion_mem_candidateMoves (s t : Square) (k : PromotionKind) :
    .promotion s t k ∈ candidateMoves := by
  cases k <;>
    simp [candidateMoves, promotionCandidates, squarePairs, allPromotionKinds]

theorem enPassant_mem_candidateMoves (s t : Square) :
    .enPassant s t ∈ candidateMoves := by
  simp [candidateMoves, enPassantCandidates, squarePairs]

theorem castle_mem_candidateMoves (m : Move)
    (h : m.isCastle = true) : m ∈ candidateMoves := by
  cases m <;> simp [Move.isCastle, candidateMoves, castleCandidates] at h ⊢

theorem mem_candidateMoves (m : Move) : m ∈ candidateMoves := by
  cases m with
  | normal s t => exact normal_mem_candidateMoves s t
  | promotion s t k => exact promotion_mem_candidateMoves s t k
  | enPassant s t => exact enPassant_mem_candidateMoves s t
  | whiteKingCastle => simp [candidateMoves, castleCandidates]
  | whiteQueenCastle => simp [candidateMoves, castleCandidates]
  | blackKingCastle => simp [candidateMoves, castleCandidates]
  | blackQueenCastle => simp [candidateMoves, castleCandidates]

theorem legalMoves_correct (p : Position) (m : Move) :
    m ∈ legalMoves p ↔ legalMove p m := by
  have hc : m ∈ candidateMoves := mem_candidateMoves m
  simp only [legalMoves, List.mem_filter, hc, true_and, decide_eq_true_eq]

theorem legalMoves_sound {p : Position} {m : Move} (h : m ∈ legalMoves p) :
    legalMove p m := (legalMoves_correct p m).1 h

theorem legalMoves_complete {p : Position} {m : Move} (h : legalMove p m) :
    m ∈ legalMoves p := (legalMoves_correct p m).2 h

end Chess
