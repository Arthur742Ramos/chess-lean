import Chess.Basic

/-!
# Board geometry and unobstructed rays

The public predicates are proposition wrappers around total Boolean
evaluators. This keeps the mathematical interface readable while ensuring
that move generation and attack queries reduce by kernel computation.
-/

namespace Chess

def sameFileB (s t : Square) : Bool := s.1 == t.1

def sameRankB (s t : Square) : Bool := s.2 == t.2

def sameFile (s t : Square) : Prop := sameFileB s t = true

def sameRank (s t : Square) : Prop := sameRankB s t = true

def absDiff (a b : Fin 8) : Nat :=
  if b.val ≤ a.val then a.val - b.val else b.val - a.val

def ltB (a b : Fin 8) : Bool := decide (a.val < b.val)

def betweenCoordB (a u b : Fin 8) : Bool :=
  (ltB a u && ltB u b) || (ltB b u && ltB u a)

def betweenCoord (a u b : Fin 8) : Prop := betweenCoordB a u b = true

def sameDiagonalB (s t : Square) : Bool :=
  (s != t) && (absDiff s.1 t.1 == absDiff s.2 t.2)

def sameDiagonal (s t : Square) : Prop := sameDiagonalB s t = true

def rookGeometryB (s t : Square) : Bool :=
  (s != t) && (sameFileB s t || sameRankB s t)

def rookGeometry (s t : Square) : Prop := rookGeometryB s t = true

def bishopGeometryB (s t : Square) : Bool := sameDiagonalB s t

def bishopGeometry (s t : Square) : Prop := bishopGeometryB s t = true

def queenGeometryB (s t : Square) : Bool :=
  rookGeometryB s t || bishopGeometryB s t

def queenGeometry (s t : Square) : Prop := queenGeometryB s t = true

def knightGeometryB (s t : Square) : Bool :=
  (s != t) &&
    ((absDiff s.1 t.1 == 1 && absDiff s.2 t.2 == 2) ||
      (absDiff s.1 t.1 == 2 && absDiff s.2 t.2 == 1))

def knightGeometry (s t : Square) : Prop := knightGeometryB s t = true

def kingGeometryB (s t : Square) : Bool :=
  (s != t) && absDiff s.1 t.1 ≤ 1 && absDiff s.2 t.2 ≤ 1

def kingGeometry (s t : Square) : Prop := kingGeometryB s t = true

def pawnMoveGeometryB (c : Color) (s t : Square) : Bool :=
  (s.1 == t.1) &&
    if c = .white then t.2.val == s.2.val + 1 else s.2.val == t.2.val + 1

def pawnMoveGeometry (c : Color) (s t : Square) : Prop :=
  pawnMoveGeometryB c s t = true

def pawnAttackGeometryB (c : Color) (s t : Square) : Bool :=
  (absDiff s.1 t.1 == 1) &&
    if c = .white then t.2.val == s.2.val + 1 else s.2.val == t.2.val + 1

def pawnAttackGeometry (c : Color) (s t : Square) : Prop :=
  pawnAttackGeometryB c s t = true

def pawnDoubleGeometryB (c : Color) (s t : Square) : Bool :=
  (s.1 == t.1) &&
    if c = .white then
      s.2.val == 1 && t.2.val == s.2.val + 2
    else
      s.2.val == 6 && s.2.val == t.2.val + 2

def pawnDoubleGeometry (c : Color) (s t : Square) : Prop :=
  pawnDoubleGeometryB c s t = true

def pieceGeometryB (k : PieceKind) (c : Color) (s t : Square) : Bool :=
  match k with
  | .king => kingGeometryB s t
  | .queen => queenGeometryB s t
  | .rook => rookGeometryB s t
  | .bishop => bishopGeometryB s t
  | .knight => knightGeometryB s t
  | .pawn => pawnMoveGeometryB c s t || pawnAttackGeometryB c s t || pawnDoubleGeometryB c s t

def pieceGeometry (k : PieceKind) (c : Color) (s t : Square) : Prop :=
  pieceGeometryB k c s t = true

def betweenB (s u t : Square) : Bool :=
  (s != u) && (u != t) &&
    ((sameFileB s t && s.1 == u.1 && betweenCoordB s.2 u.2 t.2) ||
      (sameRankB s t && s.2 == u.2 && betweenCoordB s.1 u.1 t.1) ||
      (sameDiagonalB s t &&
        absDiff s.1 u.1 == absDiff s.2 u.2 &&
        betweenCoordB s.1 u.1 t.1 && betweenCoordB s.2 u.2 t.2))

def between (s u t : Square) : Prop := betweenB s u t = true

def squaresBetween (s t : Square) : List Square :=
  allSquares.filter (fun u => betweenB s u t)

def clearBetweenB (b : Board) (s t : Square) : Bool :=
  (squaresBetween s t).all (fun u => b u == none)

def clearBetween (b : Board) (s t : Square) : Prop :=
  clearBetweenB b s t = true

theorem sameFile_refl (s : Square) : sameFile s s := by
  simp [sameFile, sameFileB]

theorem sameRank_refl (s : Square) : sameRank s s := by
  simp [sameRank, sameRankB]

theorem between_not_source {s u t : Square} (h : between s u t) : s ≠ u := by
  intro hsu
  subst hsu
  simp [between, betweenB] at h

theorem between_not_destination {s u t : Square} (h : between s u t) : u ≠ t := by
  intro hut
  subst hut
  simp [between, betweenB] at h

theorem squaresBetween_spec (s t u : Square) :
    u ∈ squaresBetween s t ↔ u ∈ allSquares ∧ between s u t := by
  simp [squaresBetween, between]

theorem clearBetween_iff (b : Board) (s t : Square) :
    clearBetween b s t ↔ ∀ u, u ∈ allSquares → between s u t → b u = none := by
  simp [clearBetween, clearBetweenB, squaresBetween_spec]

end Chess
