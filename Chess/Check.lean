import Chess.Attacks

/-! # Check and king lookup -/

namespace Chess

def kingSquare (b : Board) (c : Color) : Option Square :=
  allSquares.find? (fun s => b s = some ⟨c, .king⟩)

def inCheckB (p : Position) (c : Color) : Bool :=
  match kingSquare p.board c with
  | some s => isAttackedB p (Color.opposite c) s
  | none => true

def inCheck (p : Position) (c : Color) : Prop :=
  inCheckB p c = true

theorem kingSquare_some {b : Board} {c : Color} {s : Square}
    (h : kingSquare b c = some s) : s ∈ allSquares ∧ b s = some ⟨c, .king⟩ := by
  have h' : allSquares.find? (fun u => decide (b u = some ⟨c, .king⟩)) = some s := by
    simpa [kingSquare] using h
  constructor
  · exact List.mem_of_find?_eq_some h'
  · simpa using (List.find?_some h')

theorem kingSquare_none_iff (b : Board) (c : Color) :
    kingSquare b c = none ↔ ∀ s, b s ≠ some ⟨c, .king⟩ := by
  simp [kingSquare]

theorem inCheck_iff {p : Position} {c : Color} {s : Square}
    (h : kingSquare p.board c = some s) :
    inCheck p c ↔ isAttacked p (Color.opposite c) s := by
  simp [inCheck, inCheckB, h, isAttacked]

theorem inCheckB_eq_true_iff (p : Position) (c : Color) :
    inCheckB p c = true ↔ inCheck p c := Iff.rfl

end Chess
