import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-!
# Palomar target: complete orthodox legal-move generation

This Challenge exposes the full production rule kernel rather than a reduced
registry surrogate. Positions carry castling rights and en-passant targets;
the move datatype contains normal moves, promotions, en-passant captures, and
all four castling moves. The selected theorem is the universal production
generator correspondence `Chess.legalMoves_correct`.
-/

/-!
# The finite state model for orthodox chess

This module is the Lean counterpart of the finite board, position, and move
foundations in the Isabelle development. Coordinates are represented by
`Fin 8`, so all board operations are total and executable.
-/

namespace Chess

inductive Color where
  | white
  | black
  deriving DecidableEq, Repr

namespace Color

def opposite : Color → Color
  | .white => .black
  | .black => .white

@[simp] theorem opposite_white : opposite .white = .black := rfl
@[simp] theorem opposite_black : opposite .black = .white := rfl

@[simp] theorem opposite_opposite (c : Color) : opposite (opposite c) = c := by
  cases c <;> rfl

end Color

inductive PieceKind where
  | king
  | queen
  | rook
  | bishop
  | knight
  | pawn
  deriving DecidableEq, Repr

structure Piece where
  color : Color
  kind : PieceKind
  deriving DecidableEq, Repr

abbrev Square := Fin 8 × Fin 8
abbrev Board := Square → Option Piece

def allFiles : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

def allRanks : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

def allSquares : List Square :=
  allFiles.flatMap (fun f => allRanks.map (fun r => (f, r)))

@[simp] theorem mem_allSquares (s : Square) : s ∈ allSquares := by
  rcases s with ⟨f, r⟩
  fin_cases f <;> fin_cases r <;> simp [allSquares, allFiles, allRanks]

theorem allSquares_nodup : allSquares.Nodup := by
  native_decide

theorem allSquares_length : allSquares.length = 64 := by
  native_decide

theorem square_ext {s t : Square} (h₁ : s.1 = t.1) (h₂ : s.2 = t.2) : s = t := by
  cases s
  cases t
  simp_all

def pieceAt (b : Board) (s : Square) : Option Piece := b s

def boardUpdate (b : Board) (s : Square) (value : Option Piece) : Board :=
  Function.update b s value

def boardMove (b : Board) (source destination : Square) : Board :=
  boardUpdate (boardUpdate b source none) destination (b source)

def hasPiece (b : Board) (s : Square) (c : Color) (k : PieceKind) : Prop :=
  b s = some ⟨c, k⟩

def squaresOf (b : Board) (c : Color) (k : PieceKind) : Finset Square :=
  Finset.univ.filter (fun s => b s = some ⟨c, k⟩)

def exactlyOneKing (b : Board) (c : Color) : Prop :=
  (squaresOf b c .king).card = 1

def pawnOnPromotionRank (b : Board) : Prop :=
  ∃ s c, (s.2.val = 0 ∨ s.2.val = 7) ∧ hasPiece b s c .pawn

inductive CastleRight where
  | whiteKingSide
  | whiteQueenSide
  | blackKingSide
  | blackQueenSide
  deriving DecidableEq, Fintype, Repr

def rightColor : CastleRight → Color
  | .whiteKingSide => .white
  | .whiteQueenSide => .white
  | .blackKingSide => .black
  | .blackQueenSide => .black

def rightKingSquare : CastleRight → Square
  | .whiteKingSide => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenSide => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | .blackKingSide => (⟨4, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenSide => (⟨4, by decide⟩, ⟨7, by decide⟩)

def rightRookSquare : CastleRight → Square
  | .whiteKingSide => (⟨7, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenSide => (⟨0, by decide⟩, ⟨0, by decide⟩)
  | .blackKingSide => (⟨7, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenSide => (⟨0, by decide⟩, ⟨7, by decide⟩)

structure Position where
  board : Board
  turn : Color
  castling : Finset CastleRight
  enPassant : Option Square
  halfmove : Nat
  fullmove : Nat

def rightsConsistent (p : Position) : Prop :=
  ∀ r ∈ p.castling,
    hasPiece p.board (rightKingSquare r) (rightColor r) .king ∧
      hasPiece p.board (rightRookSquare r) (rightColor r) .rook

def positionInvariant (p : Position) : Prop :=
  exactlyOneKing p.board .white ∧
    exactlyOneKing p.board .black ∧
    ¬ pawnOnPromotionRank p.board ∧
    rightsConsistent p ∧
    0 < p.fullmove

def backRank (c : Color) (f : Fin 8) : Option Piece :=
  match f.val with
  | 0 | 7 => some ⟨c, .rook⟩
  | 1 | 6 => some ⟨c, .knight⟩
  | 2 | 5 => some ⟨c, .bishop⟩
  | 3 => some ⟨c, .queen⟩
  | 4 => some ⟨c, .king⟩
  | _ => none

def initialPiece (s : Square) : Option Piece :=
  if s.2.val = 1 then
    some ⟨.white, .pawn⟩
  else if s.2.val = 6 then
    some ⟨.black, .pawn⟩
  else if s.2.val = 0 then
    backRank .white s.1
  else if s.2.val = 7 then
    backRank .black s.1
  else
    none

def initialPosition : Position :=
  { board := initialPiece
    turn := .white
    castling := {.whiteKingSide, .whiteQueenSide, .blackKingSide, .blackQueenSide}
    enPassant := none
    halfmove := 0
    fullmove := 1 }

inductive PromotionKind where
  | queen
  | rook
  | bishop
  | knight
  deriving DecidableEq, Repr

def PromotionKind.toPieceKind : PromotionKind → PieceKind
  | .queen => .queen
  | .rook => .rook
  | .bishop => .bishop
  | .knight => .knight

def allPromotionKinds : List PromotionKind :=
  [.queen, .rook, .bishop, .knight]

inductive Move where
  | normal (source destination : Square)
  | promotion (source destination : Square) (kind : PromotionKind)
  | enPassant (source destination : Square)
  | whiteKingCastle
  | whiteQueenCastle
  | blackKingCastle
  | blackQueenCastle
  deriving DecidableEq, Repr

def Move.source : Move → Square
  | .normal s _ => s
  | .promotion s _ _ => s
  | .enPassant s _ => s
  | .whiteKingCastle => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenCastle => (⟨4, by decide⟩, ⟨0, by decide⟩)
  | .blackKingCastle => (⟨4, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenCastle => (⟨4, by decide⟩, ⟨7, by decide⟩)

def Move.destination : Move → Square
  | .normal _ t => t
  | .promotion _ t _ => t
  | .enPassant _ t => t
  | .whiteKingCastle => (⟨6, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenCastle => (⟨2, by decide⟩, ⟨0, by decide⟩)
  | .blackKingCastle => (⟨6, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenCastle => (⟨2, by decide⟩, ⟨7, by decide⟩)

def Move.promotionKind : Move → Option PromotionKind
  | .promotion _ _ k => some k
  | _ => none

def Move.isCastle : Move → Bool
  | .whiteKingCastle | .whiteQueenCastle | .blackKingCastle | .blackQueenCastle => true
  | _ => false

def Move.isEnPassant : Move → Bool
  | .enPassant _ _ => true
  | _ => false

def promotionRank : Color → Fin 8
  | .white => ⟨7, by decide⟩
  | .black => ⟨0, by decide⟩

def castleRightOf : Move → Option CastleRight
  | .whiteKingCastle => some .whiteKingSide
  | .whiteQueenCastle => some .whiteQueenSide
  | .blackKingCastle => some .blackKingSide
  | .blackQueenCastle => some .blackQueenSide
  | _ => none

def castleColorOf : Move → Option Color
  | .whiteKingCastle | .whiteQueenCastle => some .white
  | .blackKingCastle | .blackQueenCastle => some .black
  | _ => none

def castleRookSource : Move → Option Square
  | .whiteKingCastle => some (⟨7, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenCastle => some (⟨0, by decide⟩, ⟨0, by decide⟩)
  | .blackKingCastle => some (⟨7, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenCastle => some (⟨0, by decide⟩, ⟨7, by decide⟩)
  | _ => none

def castleRookDestination : Move → Option Square
  | .whiteKingCastle => some (⟨5, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenCastle => some (⟨3, by decide⟩, ⟨0, by decide⟩)
  | .blackKingCastle => some (⟨5, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenCastle => some (⟨3, by decide⟩, ⟨7, by decide⟩)
  | _ => none

def castleTransitSquare : Move → Option Square
  | .whiteKingCastle => some (⟨5, by decide⟩, ⟨0, by decide⟩)
  | .whiteQueenCastle => some (⟨3, by decide⟩, ⟨0, by decide⟩)
  | .blackKingCastle => some (⟨5, by decide⟩, ⟨7, by decide⟩)
  | .blackQueenCastle => some (⟨3, by decide⟩, ⟨7, by decide⟩)
  | _ => none

def epCapturedSquare (c : Color) (t : Square) : Option Square :=
  if c = .white ∧ t.2.val = 5 then
    some (t.1, ⟨4, by omega⟩)
  else if c = .black ∧ t.2.val = 2 then
    some (t.1, ⟨3, by omega⟩)
  else
    none

@[simp] theorem initialPosition_fullmove : initialPosition.fullmove = 1 := rfl

theorem hasPiece_iff (b : Board) (s : Square) (c : Color) (k : PieceKind) :
    hasPiece b s c k ↔ b s = some ⟨c, k⟩ := Iff.rfl

theorem allPromotionKinds_complete (k : PromotionKind) : k ∈ allPromotionKinds := by
  cases k <;> simp [allPromotionKinds]

theorem promotionRank_white : promotionRank .white = ⟨7, by decide⟩ := rfl
theorem promotionRank_black : promotionRank .black = ⟨0, by decide⟩ := rfl

end Chess


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


/-!
# Pseudo-legal and legal moves

The rule predicates are proposition-level views of total Boolean evaluators.
This mirrors the executable Isabelle definitions while giving downstream
theorems a readable logical interface.
-/

namespace Chess

def destinationFriendlyB (p : Position) (c : Color) (t : Square) : Bool :=
  match p.board t with
  | none => true
  | some q => (q.color != c) && (q.kind != .king)

def destinationFriendly (p : Position) (c : Color) (t : Square) : Prop :=
  destinationFriendlyB p c t = true

def castleEmptySquares : Move → List Square
  | .whiteKingCastle => [(⟨5, by decide⟩, ⟨0, by decide⟩), (⟨6, by decide⟩, ⟨0, by decide⟩)]
  | .whiteQueenCastle =>
      [(⟨1, by decide⟩, ⟨0, by decide⟩), (⟨2, by decide⟩, ⟨0, by decide⟩),
        (⟨3, by decide⟩, ⟨0, by decide⟩)]
  | .blackKingCastle => [(⟨5, by decide⟩, ⟨7, by decide⟩), (⟨6, by decide⟩, ⟨7, by decide⟩)]
  | .blackQueenCastle =>
      [(⟨1, by decide⟩, ⟨7, by decide⟩), (⟨2, by decide⟩, ⟨7, by decide⟩),
        (⟨3, by decide⟩, ⟨7, by decide⟩)]
  | _ => []

def castleClearB (p : Position) (m : Move) : Bool :=
  (castleEmptySquares m).all (fun s => p.board s == none)

def castleClear (p : Position) (m : Move) : Prop :=
  castleClearB p m = true

def pseudoLegalCastleB (p : Position) (m : Move) : Bool :=
  match castleColorOf m, castleRightOf m, castleRookSource m with
  | some c, some r, some rs =>
      (p.turn == c) &&
        decide (r ∈ p.castling) &&
        (p.board (if c = .white then (⟨4, by decide⟩, ⟨0, by decide⟩)
          else (⟨4, by decide⟩, ⟨7, by decide⟩)) == some ⟨c, .king⟩) &&
        (p.board rs == some ⟨c, .rook⟩) && castleClearB p m
  | _, _, _ => false

def pseudoLegalCastle (p : Position) (m : Move) : Prop :=
  pseudoLegalCastleB p m = true

def pseudoLegalEnPassantB (p : Position) (m : Move) : Bool :=
  match m with
  | .enPassant s t =>
      match p.enPassant with
      | some ep =>
          (ep == t) &&
            match p.board s with
            | some q =>
                (q.color == p.turn) && (q.kind == .pawn) &&
                  pawnAttackGeometryB p.turn s t && (p.board t == none) &&
                  match epCapturedSquare p.turn t with
                  | some cs => p.board cs == some ⟨Color.opposite p.turn, .pawn⟩
                  | none => false
            | none => false
      | none => false
  | _ => false

def pseudoLegalEnPassant (p : Position) (m : Move) : Prop :=
  pseudoLegalEnPassantB p m = true

def pseudoLegalPromotionB (p : Position) (m : Move) : Bool :=
  match m with
  | .promotion s t _ =>
      match p.board s with
      | some q =>
          (q.color == p.turn) && (q.kind == .pawn) && (t.2 == promotionRank p.turn) &&
            ((pawnMoveGeometryB p.turn s t && (p.board t == none)) ||
              (pawnAttackGeometryB p.turn s t &&
                match p.board t with
                | some q' => (q'.color == Color.opposite p.turn) && (q'.kind != .king)
                | none => false))
      | none => false
  | _ => false

def pseudoLegalPromotion (p : Position) (m : Move) : Prop :=
  pseudoLegalPromotionB p m = true

def normalPieceGeometryB (p : Position) (c : Color) (q : Piece)
    (s t : Square) : Bool :=
  match q.kind with
  | .rook => rookGeometryB s t && clearBetweenB p.board s t
  | .bishop => bishopGeometryB s t && clearBetweenB p.board s t
  | .queen => queenGeometryB s t && clearBetweenB p.board s t
  | .knight => knightGeometryB s t
  | .king => kingGeometryB s t
  | .pawn =>
      (pawnMoveGeometryB c s t && (p.board t == none)) ||
        (pawnAttackGeometryB c s t &&
          match p.board t with
          | some q' => q'.color == Color.opposite c
          | none => false) ||
        (pawnDoubleGeometryB c s t && (p.board t == none) && clearBetweenB p.board s t)

def normalPieceGeometry (p : Position) (c : Color) (q : Piece)
    (s t : Square) : Prop :=
  normalPieceGeometryB p c q s t = true

def normalPseudoLegalB (p : Position) (s t : Square) : Bool :=
  match p.board s with
  | some q =>
      (q.color == p.turn) && destinationFriendlyB p p.turn t &&
        ((q.kind != .pawn) || (t.2 != promotionRank p.turn)) &&
        normalPieceGeometryB p p.turn q s t
  | none => false

def normalPseudoLegal (p : Position) (s t : Square) : Prop :=
  normalPseudoLegalB p s t = true

def pseudoLegalB (p : Position) (m : Move) : Bool :=
  match m with
  | .normal s t => normalPseudoLegalB p s t
  | .promotion _ _ _ => pseudoLegalPromotionB p m
  | .enPassant _ _ => pseudoLegalEnPassantB p m
  | .whiteKingCastle | .whiteQueenCastle | .blackKingCastle | .blackQueenCastle =>
      pseudoLegalCastleB p m

def pseudoLegal (p : Position) (m : Move) : Prop :=
  pseudoLegalB p m = true

def castleSafeSquaresB (p : Position) (m : Move) : Bool :=
  match castleColorOf m, castleTransitSquare m with
  | some c, some u =>
      (!isAttackedB p (Color.opposite c) m.source) &&
        (!isAttackedB p (Color.opposite c) u) &&
        (!isAttackedB p (Color.opposite c) m.destination)
  | _, _ => false

def castleSafeSquares (p : Position) (m : Move) : Prop :=
  castleSafeSquaresB p m = true

def inCheckDecidable (p : Position) (c : Color) : Decidable (inCheck p c) := by
  change Decidable (inCheckB p c = true)
  infer_instance

def pseudoLegalDecidable (p : Position) (m : Move) : Decidable (pseudoLegal p m) := by
  change Decidable (pseudoLegalB p m = true)
  infer_instance

def legalMoveB (p : Position) (m : Move) : Bool :=
  pseudoLegalB p m &&
    (!inCheckB (applyMove p m) p.turn) &&
    ((!m.isCastle) || castleSafeSquaresB p m)

def legalMove (p : Position) (m : Move) : Prop :=
  pseudoLegal p m ∧
    ¬ inCheck (applyMove p m) p.turn ∧
    (¬ m.isCastle ∨ castleSafeSquares p m)

theorem legalMove_iff_legalMoveB (p : Position) (m : Move) :
    legalMove p m ↔ legalMoveB p m = true := by
  cases m <;>
    simp [legalMove, legalMoveB, pseudoLegal, inCheck, castleSafeSquares,
      pseudoLegalB, inCheckB, castleSafeSquaresB, and_assoc]

def legalMoveDecidable (p : Position) (m : Move) : Decidable (legalMove p m) := by
  if h : legalMoveB p m = true then
    exact isTrue ((legalMove_iff_legalMoveB p m).2 h)
  else
    exact isFalse (fun hp => h ((legalMove_iff_legalMoveB p m).1 hp))

theorem legalMove_kingSafe {p : Position} {m : Move} (h : legalMove p m) :
    ¬ inCheck (applyMove p m) p.turn := h.2.1

theorem legalMove_pseudoLegal {p : Position} {m : Move} (h : legalMove p m) :
    pseudoLegal p m := h.1

end Chess


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
  sorry

theorem legalMoves_sound {p : Position} {m : Move} (h : m ∈ legalMoves p) :
    legalMove p m := (legalMoves_correct p m).1 h

theorem legalMoves_complete {p : Position} {m : Move} (h : legalMove p m) :
    m ∈ legalMoves p := (legalMoves_correct p m).2 h

end Chess
