import Chess.History
import Chess.Check

/-! # Terminal game states and FIDE draw predicates -/

namespace Chess

def checkmateB (p : Position) : Bool :=
  (inCheckB p p.turn) && (legalMoves p).isEmpty

def checkmate (p : Position) : Prop := checkmateB p = true

def stalemateB (p : Position) : Bool :=
  (!inCheckB p p.turn) && (legalMoves p).isEmpty

def stalemate (p : Position) : Prop := stalemateB p = true

def deadPosition (p : Position) : Prop :=
  ¬ ∃ q, reachableFrom p q ∧ checkmate q

def fiftyMoveClaimable (p : Position) : Prop := 100 ≤ p.halfmove

def seventyFiveMoveDraw (p : Position) : Prop := 150 ≤ p.halfmove

def drawByRepetition (hs : List Position) : Prop := fivefoldRepetition hs

def kingsOnlyMaterial (p : Position) : Prop :=
  ∀ s, ∀ q, p.board s = some q → q.kind = .king

inductive DrawReason where
  | repetitionDraw
  | fiftyMoveDraw
  | seventyFiveMoveDraw
  | deadPositionDraw
  | stalemateDraw
  deriving DecidableEq, Repr

inductive GameStatus where
  | whiteWin
  | blackWin
  | automaticDraw (reason : DrawReason)
  | claimableDraw (reason : DrawReason)
  | ongoing
  deriving DecidableEq, Repr

noncomputable def gameStatus (hs : List Position) : GameStatus := by
  classical
  exact match hs.getLast? with
  | none => .ongoing
  | some p =>
      if checkmateB p then
        if p.turn = .white then .blackWin else .whiteWin
      else if stalemateB p then
        .automaticDraw .stalemateDraw
      else if deadPosition p then
        .automaticDraw .deadPositionDraw
      else if fivefoldRepetition hs then
        .automaticDraw .repetitionDraw
      else if p.halfmove ≥ 150 then
        .automaticDraw .seventyFiveMoveDraw
      else if threefoldClaimable hs then
        .claimableDraw .repetitionDraw
      else if p.halfmove ≥ 100 then
        .claimableDraw .fiftyMoveDraw
      else
        .ongoing

theorem checkmate_not_stalemate {p : Position} (h : checkmate p) :
    ¬ stalemate p := by
  intro hs
  have hc : checkmateB p = true := h
  have hs' : stalemateB p = true := hs
  have hin : inCheckB p p.turn = true := by
    have hc' : inCheckB p p.turn = true ∧ (legalMoves p).isEmpty = true := by
      simpa [checkmateB] using hc
    exact hc'.1
  have hnot : inCheckB p p.turn = false := by
    have hs'' : inCheckB p p.turn = false ∧ (legalMoves p).isEmpty = true := by
      simpa [stalemateB] using hs'
    exact hs''.1
  exact Bool.noConfusion (hin.symm.trans hnot)

end Chess
