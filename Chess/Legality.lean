import Chess.Check
import Chess.Transition

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
