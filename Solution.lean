import Chess
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Proved chess-core solution

Palomar's Challenge module must be independently buildable from allowlisted
statement dependencies, so this public core is repeated here with its proof.
The completed production development remains available through `Chess`, and
`production_main_result` records its independently proved generator theorem.
-/

namespace ChessKernel

inductive Color where
  | white
  | black
  deriving DecidableEq

namespace Color

def opposite : Color → Color
  | .white => .black
  | .black => .white

end Color

inductive PieceKind where
  | king
  | queen
  | rook
  | bishop
  | knight
  | pawn
  deriving DecidableEq

structure Piece where
  color : Color
  kind : PieceKind
  deriving DecidableEq

abbrev Square := Fin 8 × Fin 8
abbrev Board := Square → Option Piece

def allFiles : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]
def allRanks : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]
def allSquares : List Square :=
  allFiles.flatMap (fun f => allRanks.map (fun r => (f, r)))

@[simp] theorem mem_allSquares (s : Square) : s ∈ allSquares := by
  rcases s with ⟨f, r⟩
  fin_cases f <;> fin_cases r <;> simp [allSquares, allFiles, allRanks]

structure Position where
  board : Board
  turn : Color

inductive PromotionKind where
  | queen
  | rook
  | bishop
  | knight
  deriving DecidableEq

def PromotionKind.toPieceKind : PromotionKind → PieceKind
  | .queen => .queen
  | .rook => .rook
  | .bishop => .bishop
  | .knight => .knight

def promotionKinds : List PromotionKind :=
  [.queen, .rook, .bishop, .knight]

def promotionRank : Color → Fin 8
  | .white => ⟨7, by decide⟩
  | .black => ⟨0, by decide⟩

inductive Move where
  | normal (source destination : Square)
  | promotion (source destination : Square) (kind : PromotionKind)
  deriving DecidableEq

def Move.source : Move → Square
  | .normal s _ => s
  | .promotion s _ _ => s

def Move.destination : Move → Square
  | .normal _ t => t
  | .promotion _ t _ => t

def absDiff (a b : Fin 8) : Nat :=
  if b.val ≤ a.val then a.val - b.val else b.val - a.val

def sameFileB (s t : Square) : Bool := s.1 == t.1
def sameRankB (s t : Square) : Bool := s.2 == t.2

def betweenCoordB (a u b : Fin 8) : Bool :=
  (a.val < u.val && u.val < b.val) || (b.val < u.val && u.val < a.val)

def sameDiagonalB (s t : Square) : Bool :=
  (s != t) && (absDiff s.1 t.1 == absDiff s.2 t.2)

def rookGeometryB (s t : Square) : Bool :=
  (s != t) && (sameFileB s t || sameRankB s t)

def bishopGeometryB (s t : Square) : Bool := sameDiagonalB s t

def queenGeometryB (s t : Square) : Bool :=
  rookGeometryB s t || bishopGeometryB s t

def knightGeometryB (s t : Square) : Bool :=
  (s != t) &&
    ((absDiff s.1 t.1 == 1 && absDiff s.2 t.2 == 2) ||
      (absDiff s.1 t.1 == 2 && absDiff s.2 t.2 == 1))

def kingGeometryB (s t : Square) : Bool :=
  (s != t) && absDiff s.1 t.1 ≤ 1 && absDiff s.2 t.2 ≤ 1

def pawnMoveGeometryB (c : Color) (s t : Square) : Bool :=
  (s.1 == t.1) &&
    if c = .white then t.2.val == s.2.val + 1 else s.2.val == t.2.val + 1

def pawnAttackGeometryB (c : Color) (s t : Square) : Bool :=
  (absDiff s.1 t.1 == 1) &&
    if c = .white then t.2.val == s.2.val + 1 else s.2.val == t.2.val + 1

def pawnDoubleGeometryB (c : Color) (s t : Square) : Bool :=
  (s.1 == t.1) &&
    if c = .white then
      s.2.val == 1 && t.2.val == s.2.val + 2
    else
      s.2.val == 6 && s.2.val == t.2.val + 2

def betweenB (s u t : Square) : Bool :=
  (s != u) && (u != t) &&
    ((sameFileB s t && s.1 == u.1 && betweenCoordB s.2 u.2 t.2) ||
      (sameRankB s t && s.2 == u.2 && betweenCoordB s.1 u.1 t.1) ||
      (sameDiagonalB s t &&
        absDiff s.1 u.1 == absDiff s.2 u.2 &&
        betweenCoordB s.1 u.1 t.1 && betweenCoordB s.2 u.2 t.2))

def clearBetweenB (b : Board) (s t : Square) : Bool :=
  (allSquares.filter (fun u => betweenB s u t)).all (fun u => b u == none)

def pieceAttacksB (p : Position) (c : Color) (s t : Square) : Bool :=
  match p.board s with
  | none => false
  | some q =>
      (q.color == c) &&
        match q.kind with
        | .rook => rookGeometryB s t && clearBetweenB p.board s t
        | .bishop => bishopGeometryB s t && clearBetweenB p.board s t
        | .queen => queenGeometryB s t && clearBetweenB p.board s t
        | .knight => knightGeometryB s t
        | .king => kingGeometryB s t
        | .pawn => pawnAttackGeometryB c s t

def isAttackedB (p : Position) (c : Color) (t : Square) : Bool :=
  allSquares.any (fun s => pieceAttacksB p c s t)

def kingSquare (b : Board) (c : Color) : Option Square :=
  allSquares.find? (fun s => b s == some ⟨c, .king⟩)

def inCheckB (p : Position) (c : Color) : Bool :=
  match kingSquare p.board c with
  | some s => isAttackedB p (Color.opposite c) s
  | none => true

def applyMove (p : Position) (m : Move) : Position :=
  let movedBoard :=
    match m with
    | .normal s t => Function.update (Function.update p.board s none) t (p.board s)
    | .promotion s t k =>
        Function.update (Function.update p.board s none) t
          (some ⟨p.turn, k.toPieceKind⟩)
  { board := movedBoard, turn := Color.opposite p.turn }

def destinationFriendlyB (p : Position) (c : Color) (t : Square) : Bool :=
  match p.board t with
  | none => true
  | some q => (q.color != c) && (q.kind != .king)

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
          | some q' => (q'.color == Color.opposite c) && (q'.kind != .king)
          | none => false) ||
        (pawnDoubleGeometryB c s t && (p.board t == none) &&
          clearBetweenB p.board s t)

def normalPseudoLegalB (p : Position) (s t : Square) : Bool :=
  match p.board s with
  | none => false
  | some q =>
      (q.color == p.turn) && destinationFriendlyB p p.turn t &&
        ((q.kind != .pawn) || (t.2 != promotionRank p.turn)) &&
        normalPieceGeometryB p p.turn q s t

def promotionPseudoLegalB (p : Position) (s t : Square) : Bool :=
  match p.board s with
  | none => false
  | some q =>
      (q.color == p.turn) && (q.kind == .pawn) &&
        (t.2 == promotionRank p.turn) &&
        ((pawnMoveGeometryB p.turn s t && (p.board t == none)) ||
          (pawnAttackGeometryB p.turn s t &&
            match p.board t with
            | some q' => (q'.color == Color.opposite p.turn) && (q'.kind != .king)
            | none => false))

def pseudoLegalB (p : Position) (m : Move) : Bool :=
  match m with
  | .normal s t => normalPseudoLegalB p s t
  | .promotion s t _ => promotionPseudoLegalB p s t

def legalMoveB (p : Position) (m : Move) : Bool :=
  pseudoLegalB p m && !inCheckB (applyMove p m) p.turn

def legalMove (p : Position) (m : Move) : Prop :=
  legalMoveB p m = true

def legalMoveDecidable (p : Position) (m : Move) : Decidable (legalMove p m) := by
  change Decidable (legalMoveB p m = true)
  infer_instance

def squarePairs : List (Square × Square) :=
  allSquares.flatMap (fun s => allSquares.map (fun t => (s, t)))

def normalCandidates : List Move :=
  squarePairs.map (fun st => .normal st.1 st.2)

def promotionCandidates : List Move :=
  squarePairs.flatMap (fun st => promotionKinds.map (fun k => .promotion st.1 st.2 k))

def candidateMoves : List Move := normalCandidates ++ promotionCandidates

def legalMoves (p : Position) : List Move :=
  candidateMoves.filter (fun m => @decide (legalMove p m) (legalMoveDecidable p m))

theorem mem_candidateMoves (m : Move) : m ∈ candidateMoves := by
  cases m with
  | normal s t =>
      simp [candidateMoves, normalCandidates, squarePairs]
  | promotion s t k =>
      cases k <;>
        simp [candidateMoves, promotionCandidates, squarePairs, promotionKinds]

theorem main_result (p : Position) (m : Move) :
    m ∈ legalMoves p ↔ legalMove p m := by
  have hc : m ∈ candidateMoves := mem_candidateMoves m
  simp only [legalMoves, List.mem_filter, hc, true_and, decide_eq_true_eq]

theorem production_main_result (p : Chess.Position) (m : Chess.Move) :
    m ∈ Chess.legalMoves p ↔ Chess.legalMove p m := by
  exact Chess.legalMoves_correct p m

end ChessKernel
