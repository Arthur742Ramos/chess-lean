import Chess.Generator

/-! # Executable perft -/

namespace Chess

def perft (p : Position) : Nat → Nat
  | 0 => 1
  | n + 1 => (legalMoves p).foldr (fun m acc => perft (applyMove p m) n + acc) 0

def perftDivide (p : Position) (n : Nat) : List (Move × Nat) :=
  (legalMoves p).map (fun m => (m, perft (applyMove p m) n))

@[simp] theorem perft_zero (p : Position) : perft p 0 = 1 := rfl

theorem perft_succ (p : Position) (n : Nat) :
    perft p (n + 1) =
      (legalMoves p).foldr (fun m acc => perft (applyMove p m) n + acc) 0 := rfl

theorem perftDivide_fst (p : Position) (n : Nat) :
    (perftDivide p n).map Prod.fst = legalMoves p := by
  simp [perftDivide, Function.comp_def]

end Chess
