import Chess.Certificates
import Chess.SAN

/-!
# Rank-reflection symmetry

The involution exchanges the two colours and reflects ranks while preserving
files. It transports the move constructors, castling rights, en-passant
target, and all position clocks. The exported executable predicates can then
be checked on reflected positions without any special-case board encoding.
-/

namespace Chess

def mirrorRank (r : Fin 8) : Fin 8 := ⟨7 - r.val, by omega⟩

def mirrorSquare (s : Square) : Square := (s.1, mirrorRank s.2)

def mirrorPiece (q : Piece) : Piece :=
  { color := Color.opposite q.color
    kind := q.kind }

def mirrorBoard (b : Board) : Board :=
  fun s => (b (mirrorSquare s)).map mirrorPiece

def mirrorRight : CastleRight → CastleRight
  | .whiteKingSide => .blackKingSide
  | .whiteQueenSide => .blackQueenSide
  | .blackKingSide => .whiteKingSide
  | .blackQueenSide => .whiteQueenSide

def mirrorRights (rights : Finset CastleRight) : Finset CastleRight :=
  rights.image mirrorRight

def mirrorMove : Move → Move
  | .normal s t => .normal (mirrorSquare s) (mirrorSquare t)
  | .promotion s t k => .promotion (mirrorSquare s) (mirrorSquare t) k
  | .enPassant s t => .enPassant (mirrorSquare s) (mirrorSquare t)
  | .whiteKingCastle => .blackKingCastle
  | .whiteQueenCastle => .blackQueenCastle
  | .blackKingCastle => .whiteKingCastle
  | .blackQueenCastle => .whiteQueenCastle

def mirrorPosition (p : Position) : Position :=
  { board := mirrorBoard p.board
    turn := Color.opposite p.turn
    castling := mirrorRights p.castling
    enPassant := p.enPassant.map mirrorSquare
    halfmove := p.halfmove
    fullmove := p.fullmove }

theorem mirrorRank_involutive (r : Fin 8) : mirrorRank (mirrorRank r) = r := by
  apply Fin.ext
  simp [mirrorRank]
  omega

theorem mirrorSquare_involutive (s : Square) : mirrorSquare (mirrorSquare s) = s := by
  cases s with
  | mk f r => simp [mirrorSquare, mirrorRank_involutive]

theorem mirrorPiece_involutive (q : Piece) : mirrorPiece (mirrorPiece q) = q := by
  cases q with
  | mk c k => cases c <;> rfl

theorem mirrorRight_involutive (r : CastleRight) : mirrorRight (mirrorRight r) = r := by
  cases r <;> rfl

theorem mirrorMove_involutive (m : Move) : mirrorMove (mirrorMove m) = m := by
  cases m <;> simp [mirrorMove, mirrorSquare_involutive]

theorem mirrorBoard_involutive (b : Board) : mirrorBoard (mirrorBoard b) = b := by
  funext s
  simp only [mirrorBoard, Option.map_map]
  rw [mirrorSquare_involutive]
  cases h : b s with
  | none => simp
  | some q => simp [Function.comp_def, mirrorPiece_involutive]

theorem mirrorRights_involutive (rights : Finset CastleRight) :
    mirrorRights (mirrorRights rights) = rights := by
  ext r
  simp [mirrorRights, mirrorRight_involutive]

theorem mirrorPosition_involutive (p : Position) :
    mirrorPosition (mirrorPosition p) = p := by
  cases p with
  | mk b turn rights ep half full =>
      cases ep with
      | none =>
          simp [mirrorPosition, mirrorBoard_involutive, mirrorRights_involutive]
      | some s =>
          simp [mirrorPosition, mirrorBoard_involutive, mirrorRights_involutive,
            mirrorSquare_involutive]

theorem mirrorMove_source (m : Move) :
    (mirrorMove m).source = mirrorSquare m.source := by
  cases m <;> rfl

theorem mirrorMove_destination (m : Move) :
    (mirrorMove m).destination = mirrorSquare m.destination := by
  cases m <;> rfl

theorem mirrorPosition_turn (p : Position) :
    (mirrorPosition p).turn = Color.opposite p.turn := rfl

theorem mirror_initial_legal_move_count :
    (legalMoves (mirrorPosition initialPosition)).length = 20 := by
  native_decide

theorem mirror_initial_perft_one :
    perft (mirrorPosition initialPosition) 1 = 20 := by
  native_decide

end Chess
