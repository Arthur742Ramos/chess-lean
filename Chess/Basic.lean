import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

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
