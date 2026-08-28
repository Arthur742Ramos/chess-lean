import Chess.Basic

/-!
# Typed FEN fields

The typed layer is intentionally lossless: it is a six-field view of a
`Position`, and parsing it reconstructs the position without a partial
semantic validation step. Textual FEN validation lives in `Chess.FENText`.
-/

namespace Chess

structure Fen where
  board : Board
  turn : Color
  castling : Finset CastleRight
  enPassant : Option Square
  halfmove : Nat
  fullmove : Nat

def printFenFields (p : Position) : Fen :=
  { board := p.board
    turn := p.turn
    castling := p.castling
    enPassant := p.enPassant
    halfmove := p.halfmove
    fullmove := p.fullmove }

def parseFenFields (f : Fen) : Option Position :=
  some
    { board := f.board
      turn := f.turn
      castling := f.castling
      enPassant := f.enPassant
      halfmove := f.halfmove
      fullmove := f.fullmove }

def serializablePosition (p : Position) : Prop := 0 < p.fullmove

theorem parseFenFields_printFenFields (p : Position) :
    parseFenFields (printFenFields p) = some p := by
  rfl

theorem printFenFields_parseFenFields {f : Fen} {p : Position}
    (h : parseFenFields f = some p) : printFenFields p = f := by
  have hpos :
      ({ board := f.board
         turn := f.turn
         castling := f.castling
         enPassant := f.enPassant
         halfmove := f.halfmove
         fullmove := f.fullmove } : Position) = p := by
    simpa [parseFenFields] using h
  cases hpos
  rfl

end Chess
