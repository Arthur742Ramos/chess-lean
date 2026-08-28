import Chess.Geometry

/-!
# Geometric attacks

Attack is deliberately independent of move legality. This is the rule-level
notion needed for check and castling: a pinned piece still attacks according
to its geometry, while sliders additionally require an unobstructed segment.
-/

namespace Chess

def sliderAttackB (p : Position) (s t : Square) : Bool :=
  clearBetweenB p.board s t

def sliderAttack (p : Position) (s t : Square) : Prop :=
  sliderAttackB p s t = true

def pieceAttacksB (p : Position) (c : Color) (s t : Square) : Bool :=
  match p.board s with
  | some q =>
      (q.color == c) &&
        ((q.kind == .rook && rookGeometryB s t && sliderAttackB p s t) ||
          (q.kind == .bishop && bishopGeometryB s t && sliderAttackB p s t) ||
          (q.kind == .queen && queenGeometryB s t && sliderAttackB p s t) ||
          (q.kind == .knight && knightGeometryB s t) ||
          (q.kind == .king && kingGeometryB s t) ||
          (q.kind == .pawn && pawnAttackGeometryB c s t))
  | none => false

def pieceAttacks (p : Position) (c : Color) (s t : Square) : Prop :=
  pieceAttacksB p c s t = true

def isAttackedB (p : Position) (c : Color) (t : Square) : Bool :=
  allSquares.any (fun s => pieceAttacksB p c s t)

def isAttacked (p : Position) (c : Color) (t : Square) : Prop :=
  isAttackedB p c t = true

def attackedSquares (p : Position) (c : Color) : List Square :=
  allSquares.filter (fun t => isAttackedB p c t)

theorem pieceAttacks_empty_source (p : Position) (c : Color) (s t : Square)
    (h : p.board s = none) : ¬ pieceAttacks p c s t := by
  simp [pieceAttacks, pieceAttacksB, h]

theorem isAttacked_iff (p : Position) (c : Color) (t : Square) :
    isAttacked p c t ↔ ∃ s, pieceAttacks p c s t := by
  simp [isAttacked, isAttackedB, pieceAttacks, pieceAttacksB]

theorem attackedSquares_correct (p : Position) (c : Color) (t : Square) :
    t ∈ attackedSquares p c ↔ isAttacked p c t := by
  simp [attackedSquares, isAttacked, isAttackedB]

end Chess
