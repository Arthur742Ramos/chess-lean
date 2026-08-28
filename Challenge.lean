import Chess.Generator

/-!
# Advertised statement

This is the small, trusted surface a mathematical reader should audit. Prefer
ordinary Mathlib definitions, document every new definition precisely, and
state every headline claim here without hiding hypotheses or weakening the
informal result.
-/

namespace ChessKernel

/--
The finite generator is extensionally exact: for every total position and
move, filtering the transparent candidate universe by the executable legality
test produces exactly the declarative legal-move relation.
-/
theorem main_result (p : Chess.Position) (m : Chess.Move) :
    m ∈ Chess.legalMoves p ↔ Chess.legalMove p m := by
  sorry

end ChessKernel
