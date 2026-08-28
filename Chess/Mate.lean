import Chess.Game
import Chess.Perft

/-!
# Bounded forced mate

The `B` definitions are executable and take terminal and claim predicates as
Boolean parameters. The logical definitions retain the Isabelle scope,
including the exact unbounded dead-position predicate; that predicate is not
silently approximated for code generation.
-/

namespace Chess

def historyCurrent (hs : List Position) : Option Position := hs.getLast?

def forcedMateWithinPolicyB (c : Color)
    (terminal : List Position → Bool)
    (claimCurrent : List Position → Bool)
    (claimAfter : List Position → Move → Bool)
    (hs : List Position) : Nat → Bool
  | 0 =>
      match historyCurrent hs with
      | none => false
      | some p => checkmateB p && (p.turn == Color.opposite c)
  | n + 1 =>
      match historyCurrent hs with
      | none => false
      | some p =>
          if checkmateB p then p.turn == Color.opposite c
          else if stalemateB p || terminal hs then false
          else if p.turn == c then
            (legalMoves p).any (fun m =>
              forcedMateWithinPolicyB c terminal claimCurrent claimAfter
                (hs ++ [applyMove p m]) n)
          else if claimCurrent hs then false
          else
            (legalMoves p).all (fun m =>
              (!claimAfter hs m) &&
                forcedMateWithinPolicyB c terminal claimCurrent claimAfter
                  (hs ++ [applyMove p m]) n)

def forcedMateWithinTerminalB (c : Color) (terminal : List Position → Bool)
    (hs : List Position) (n : Nat) : Bool :=
  forcedMateWithinPolicyB c terminal (fun _ => false) (fun _ _ => false) hs n

def executableMateTerminalB (hs : List Position) : Bool :=
  match historyCurrent hs with
  | none => true
  | some p => fivefoldRepetitionB hs || decide (150 ≤ p.halfmove)

def executableMateClaimCurrentB (hs : List Position) : Bool :=
  match historyCurrent hs with
  | none => false
  | some p =>
      threefoldClaimableB hs || decide (100 ≤ p.halfmove)

def executableMateClaimAfterB (hs : List Position) (m : Move) : Bool :=
  match historyCurrent hs with
  | none => false
  | some p =>
      threefoldClaimableAfterB hs m || fiftyMoveClaimableAfterB p m

def forcedMateWithinExecutableB (c : Color) (hs : List Position) (n : Nat) : Bool :=
  forcedMateWithinPolicyB c executableMateTerminalB executableMateClaimCurrentB
    executableMateClaimAfterB hs n

noncomputable def forcedMateWithin (c : Color) (p : Position) : Nat → Prop
  | 0 => checkmate p ∧ p.turn = Color.opposite c
  | n + 1 => by
      classical
      exact if checkmate p then p.turn = Color.opposite c
      else if stalemate p ∨ deadPosition p ∨ fivefoldRepetition [p] ∨
          (150 ≤ p.halfmove) then False
      else if p.turn = c then
        ∃ m, m ∈ legalMoves p ∧ forcedMateWithin c (applyMove p m) n
      else
        ∀ m, m ∈ legalMoves p → forcedMateWithin c (applyMove p m) n

def mateInPosition (c : Color) (p : Position) (n : Nat) : Prop :=
  forcedMateWithin c p n

noncomputable def forcedMateWithinPolicy (c : Color)
    (terminal : List Position → Prop)
    (claimCurrent : List Position → Prop)
    (claimAfter : List Position → Move → Prop)
    (hs : List Position) : Nat → Prop
  | 0 => by
      classical
      exact match historyCurrent hs with
      | none => False
      | some p => checkmate p ∧ p.turn = Color.opposite c
  | n + 1 => by
      classical
      exact match historyCurrent hs with
      | none => False
      | some p =>
          if checkmate p then p.turn = Color.opposite c
          else if stalemate p ∨ terminal hs then False
          else if p.turn = c then
            ∃ m, m ∈ legalMoves p ∧
              forcedMateWithinPolicy c terminal claimCurrent claimAfter
                (hs ++ [applyMove p m]) n
          else if claimCurrent hs then False
          else
            ∀ m, m ∈ legalMoves p →
              ¬ claimAfter hs m ∧
                forcedMateWithinPolicy c terminal claimCurrent claimAfter
                  (hs ++ [applyMove p m]) n

noncomputable def semanticMateTerminal (hs : List Position) : Prop :=
  match historyCurrent hs with
  | none => True
  | some p => deadPosition p ∨ fivefoldRepetition hs ∨ 150 ≤ p.halfmove

noncomputable def semanticMateClaimCurrent (hs : List Position) : Prop :=
  match historyCurrent hs with
  | none => False
  | some p => threefoldClaimable hs ∨ 100 ≤ p.halfmove

noncomputable def semanticMateClaimAfter (hs : List Position) (m : Move) : Prop :=
  match historyCurrent hs with
  | none => False
  | some p => threefoldClaimableAfter hs m ∨ fiftyMoveClaimableAfter p m

def forcedMateWithinTerminal (c : Color) (terminal : List Position → Prop)
    (hs : List Position) (n : Nat) : Prop :=
  forcedMateWithinPolicy c terminal (fun _ => False) (fun _ _ => False) hs n

def forcedMateWithinHistory (c : Color) (hs : List Position) (n : Nat) : Prop :=
  forcedMateWithinPolicy c semanticMateTerminal semanticMateClaimCurrent
    semanticMateClaimAfter hs n

def mateIn (c : Color) (hs : List Position) (n : Nat) : Prop :=
  forcedMateWithinHistory c hs n

theorem forcedMateWithin_zero (c : Color) (p : Position) :
    forcedMateWithin c p 0 ↔ checkmate p ∧ p.turn = Color.opposite c := Iff.rfl

theorem mateIn_iff (c : Color) (hs : List Position) (n : Nat) :
    mateIn c hs n ↔ forcedMateWithinHistory c hs n := Iff.rfl

end Chess
