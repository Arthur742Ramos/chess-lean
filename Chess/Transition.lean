import Chess.Basic

/-!
# Total state transitions

`applyMove` is total, as in the Isabelle kernel. Callers are expected to guard
it with `pseudoLegal` or `legalMove`; totality keeps transition lemmas and
executable search simple.
-/

namespace Chess

def movingPiece (p : Position) (m : Move) : Option Piece :=
  p.board m.source

def movingColor (p : Position) (m : Move) : Option Color :=
  (movingPiece p m).map Piece.color

def moveCaptureSquare (p : Position) (m : Move) : Option Square :=
  match m with
  | .normal _ t => if p.board t = none then none else some t
  | .promotion _ t _ => if p.board t = none then none else some t
  | .enPassant _ t => epCapturedSquare p.turn t
  | .whiteKingCastle | .whiteQueenCastle | .blackKingCastle | .blackQueenCastle => none

def moveIsCapture (p : Position) (m : Move) : Bool :=
  match moveCaptureSquare p m with
  | some s => (p.board s).isSome
  | none => false

def moveIsPawn (p : Position) (m : Move) : Bool :=
  match m with
  | .promotion _ _ _ | .enPassant _ _ => true
  | _ =>
      match movingPiece p m with
      | some q => q.kind = .pawn
      | none => false

def rightsRemovedForSquare (s : Square) : Finset CastleRight :=
  Finset.univ.filter (fun r => rightKingSquare r = s ∨ rightRookSquare r = s)

def rightsRemovedForMove (p : Position) (m : Move) : Finset CastleRight :=
  let touched :=
    {m.source, m.destination} ∪
      match castleRookSource m, castleRookDestination m with
      | some rs, some rd => {rs, rd}
      | _, _ => ∅
  Finset.biUnion touched rightsRemovedForSquare ∪
    match moveCaptureSquare p m with
    | some cs => rightsRemovedForSquare cs
    | none => ∅

def rightsAfterMove (p : Position) (m : Move) : Finset CastleRight :=
  p.castling \ rightsRemovedForMove p m

def castleBoard (p : Position) (m : Move) : Board :=
  match castleRookSource m, castleRookDestination m with
  | some rs, some rd => boardMove (boardMove p.board m.source m.destination) rs rd
  | _, _ => p.board

def applyBoard (p : Position) (m : Move) : Board :=
  match m with
  | .normal s t => boardMove p.board s t
  | .promotion s t k =>
      boardUpdate (boardUpdate p.board s none) t
        (some ⟨p.turn, k.toPieceKind⟩)
  | .enPassant s t =>
      match epCapturedSquare p.turn t with
      | some cs => boardUpdate (boardMove p.board s t) cs none
      | none => boardMove p.board s t
  | .whiteKingCastle | .whiteQueenCastle | .blackKingCastle | .blackQueenCastle =>
      castleBoard p m

def pawnDoubleTarget (p : Position) (m : Move) : Option Square :=
  match m with
  | .normal s t =>
      if moveIsPawn p m ∧ s.1 = t.1 ∧
          ((p.turn = .white ∧ s.2.val = 1 ∧ t.2.val = 3) ∨
            (p.turn = .black ∧ s.2.val = 6 ∧ t.2.val = 4)) then
        if p.turn = .white then some (s.1, ⟨2, by decide⟩)
        else some (s.1, ⟨5, by decide⟩)
      else none
  | _ => none

def newEnPassant (p : Position) (m : Move) : Option Square :=
  pawnDoubleTarget p m

def applyMove (p : Position) (m : Move) : Position :=
  { board := applyBoard p m
    turn := Color.opposite p.turn
    castling := rightsAfterMove p m
    enPassant := newEnPassant p m
    halfmove := if moveIsPawn p m || moveIsCapture p m then 0 else p.halfmove + 1
    fullmove := if p.turn = .black then p.fullmove + 1 else p.fullmove }

@[simp] theorem applyMove_turn (p : Position) (m : Move) :
    (applyMove p m).turn = Color.opposite p.turn := rfl

@[simp] theorem applyMove_fullmove_white (p : Position) (m : Move)
    (h : p.turn = .white) : (applyMove p m).fullmove = p.fullmove := by
  simp [applyMove, h]

@[simp] theorem applyMove_fullmove_black (p : Position) (m : Move)
    (h : p.turn = .black) : (applyMove p m).fullmove = p.fullmove + 1 := by
  simp [applyMove, h]

theorem applyMove_halfmove (p : Position) (m : Move) :
    (applyMove p m).halfmove =
      if moveIsPawn p m || moveIsCapture p m then 0 else p.halfmove + 1 := rfl

theorem applyMove_board (p : Position) (m : Move) :
    (applyMove p m).board = applyBoard p m := rfl

end Chess
