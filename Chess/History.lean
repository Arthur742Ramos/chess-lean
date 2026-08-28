import Chess.Generator

/-!
# Histories, reachability, repetition, and draw predicates

The game history is explicit. Repetition keys omit clocks and retain an
en-passant target only when an en-passant move is actually legal, matching the
rule-sensitive key used by the Isabelle development.
-/

namespace Chess

def legalTransition (p q : Position) : Prop :=
  ∃ m, legalMove p m ∧ q = applyMove p m

def reachableFrom (p q : Position) : Prop :=
  Relation.ReflTransGen legalTransition p q

def reachable (p : Position) : Prop :=
  reachableFrom initialPosition p

def legalPosition (p : Position) : Prop := reachable p

def legalStep (p : Position) (m : Move) (q : Position) : Prop :=
  legalMove p m ∧ q = applyMove p m

def replay : Position → List Move → Position
  | p, [] => p
  | p, m :: ms => replay (applyMove p m) ms

def validSteps : List Position → Prop
  | [] => True
  | [_] => True
  | p :: q :: ps => legalTransition p q ∧ validSteps (q :: ps)

def validHistory (hs : List Position) : Prop :=
  match hs with
  | [] => False
  | p :: ps => p = initialPosition ∧ validSteps (p :: ps)

def boardCode (b : Board) : List (Option Piece) := allSquares.map b

structure RepetitionKey where
  board : List (Option Piece)
  turn : Color
  castling : Finset CastleRight
  enPassant : Option Square
  deriving DecidableEq

def legalEnPassantAvailableB (p : Position) : Bool :=
  (legalMoves p).any Move.isEnPassant

def legalEnPassantAvailable (p : Position) : Prop :=
  legalEnPassantAvailableB p = true

def effectiveEnPassant (p : Position) : Option Square :=
  if legalEnPassantAvailableB p then p.enPassant else none

def repetitionKey (p : Position) : RepetitionKey :=
  { board := boardCode p.board
    turn := p.turn
    castling := p.castling
    enPassant := effectiveEnPassant p }

def keyOccurrences (k : RepetitionKey) (hs : List Position) : Nat :=
  (hs.filter (fun p => decide (repetitionKey p = k))).length

def threefoldClaimableB (hs : List Position) : Bool :=
  match hs.getLast? with
  | none => false
  | some p => decide (3 ≤ keyOccurrences (repetitionKey p) hs)

def threefoldClaimable (hs : List Position) : Prop :=
  threefoldClaimableB hs = true

def fivefoldRepetitionB (hs : List Position) : Bool :=
  match hs.getLast? with
  | none => false
  | some p => decide (5 ≤ keyOccurrences (repetitionKey p) hs)

def fivefoldRepetition (hs : List Position) : Prop :=
  fivefoldRepetitionB hs = true

def threefoldClaimableAfterB (hs : List Position) (m : Move) : Bool :=
  match hs.getLast? with
  | none => false
  | some p =>
      legalMoveB p m &&
        decide (3 ≤ keyOccurrences (repetitionKey (applyMove p m))
          (hs ++ [applyMove p m]))

def threefoldClaimableAfter (hs : List Position) (m : Move) : Prop :=
  threefoldClaimableAfterB hs m = true

def fiftyMoveClaimableAfterB (p : Position) (m : Move) : Bool :=
  legalMoveB p m && decide (100 ≤ (applyMove p m).halfmove)

def fiftyMoveClaimableAfter (p : Position) (m : Move) : Prop :=
  fiftyMoveClaimableAfterB p m = true

theorem reachableFrom_refl (p : Position) : reachableFrom p p :=
  Relation.ReflTransGen.refl

theorem reachableFrom_trans {p q r : Position} :
    reachableFrom p q → reachableFrom q r → reachableFrom p r := by
  exact Relation.ReflTransGen.trans

theorem reachableFrom_step {p q : Position} (h : reachableFrom p q)
    {m : Move} (hm : legalMove q m) : reachableFrom p (applyMove q m) := by
  exact Relation.ReflTransGen.tail h (show legalTransition q (applyMove q m) from ⟨m, hm, rfl⟩)

theorem reachable_initial : reachable initialPosition := by
  exact reachableFrom_refl initialPosition

theorem legalStep_iff {p q : Position} {m : Move} :
    legalStep p m q ↔ legalMove p m ∧ q = applyMove p m := Iff.rfl

theorem legalTransitionI {p : Position} {m : Move} (h : legalMove p m) :
    legalTransition p (applyMove p m) := ⟨m, h, rfl⟩

end Chess
