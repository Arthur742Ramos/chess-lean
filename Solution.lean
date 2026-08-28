import Chess

/-!
# Proved solution

This module may import the full proof development. Comparator checks that the
declaration below has exactly the same statement as its counterpart in
`Challenge.lean` and uses only the permitted axioms.
-/

namespace ChessKernel

theorem main_result (p : Chess.Position) (m : Chess.Move) :
    m ∈ Chess.legalMoves p ↔ Chess.legalMove p m := by
  exact Chess.legalMoves_correct p m

end ChessKernel
