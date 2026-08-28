import Chess.FENText
import Chess.Generator

/-!
# Coordinate notation and UCI

UCI deliberately identifies castling by the king's coordinate move, as the
wire protocol does. Parsing searches the verified legal-move list, so a
coordinate token cannot bypass the rule kernel.
-/

namespace Chess

structure UciMove where
  source : Square
  destination : Square
  promotion : Option PromotionKind
  deriving DecidableEq, Repr

def uciOfMove : Move → UciMove
  | .normal s t => ⟨s, t, none⟩
  | .promotion s t k => ⟨s, t, some k⟩
  | .enPassant s t => ⟨s, t, none⟩
  | .whiteKingCastle => ⟨(⟨4, by decide⟩, ⟨0, by decide⟩),
      (⟨6, by decide⟩, ⟨0, by decide⟩), none⟩
  | .whiteQueenCastle => ⟨(⟨4, by decide⟩, ⟨0, by decide⟩),
      (⟨2, by decide⟩, ⟨0, by decide⟩), none⟩
  | .blackKingCastle => ⟨(⟨4, by decide⟩, ⟨7, by decide⟩),
      (⟨6, by decide⟩, ⟨7, by decide⟩), none⟩
  | .blackQueenCastle => ⟨(⟨4, by decide⟩, ⟨7, by decide⟩),
      (⟨2, by decide⟩, ⟨7, by decide⟩), none⟩

def uciWitness (p : Position) (u : UciMove) : Prop :=
  ∃ m, legalMove p m ∧ uciOfMove m = u

def parseUciMove (p : Position) (u : UciMove) : Option Move :=
  (legalMoves p).find? (fun m => decide (uciOfMove m = u))

def printUciMove (_p : Position) (m : Move) : UciMove := uciOfMove m

def promotionChar : PromotionKind → Char
  | .queen => 'q'
  | .rook => 'r'
  | .bishop => 'b'
  | .knight => 'n'

def promotionOfChar : Char → Option PromotionKind
  | 'q' => some .queen
  | 'r' => some .rook
  | 'b' => some .bishop
  | 'n' => some .knight
  | _ => none

def uciText (u : UciMove) : String :=
  String.ofList <|
    squareText u.source ++ squareText u.destination ++
      match u.promotion with
      | some k => [promotionChar k]
      | none => []

def parseUciTextToken (cs : List Char) : Option UciMove :=
  match cs with
  | [f₁, r₁, f₂, r₂] =>
      match squareOfText [f₁, r₁], squareOfText [f₂, r₂] with
      | some s, some t => some ⟨s, t, none⟩
      | _, _ => none
  | [f₁, r₁, f₂, r₂, promotion] =>
      match squareOfText [f₁, r₁], squareOfText [f₂, r₂], promotionOfChar promotion with
      | some s, some t, some k => some ⟨s, t, some k⟩
      | _, _, _ => none
  | _ => none

def parseUciText (p : Position) (text : String) : Option Move :=
  match parseUciTextToken text.toList with
  | some u => parseUciMove p u
  | none => none

def printUciText (_p : Position) (m : Move) : String := uciText (uciOfMove m)

theorem uciOfMove_printUciMove (p : Position) (m : Move) :
    printUciMove p m = uciOfMove m := rfl

theorem parseUciText_printUciText_initial_e2e4 :
    parseUciText initialPosition "e2e4" =
      some (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩)) := by
  native_decide

end Chess
