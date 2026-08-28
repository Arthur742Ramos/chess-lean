import Chess.FEN

/-!
# Strict six-field FEN text

The parser accepts the standard six fields, rejects malformed separators and
rank widths, and reconstructs a total `Position`. The printer emits the
canonical rank order, empty-run compression, castling order, and decimal
clock representation used by orthodox FEN.
-/

namespace Chess

def splitOnCharAux (delimiter : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | c :: cs, acc =>
      if c = delimiter then
        acc.reverse :: splitOnCharAux delimiter cs []
      else
        splitOnCharAux delimiter cs (c :: acc)

def splitOnChar (delimiter : Char) (cs : List Char) : List (List Char) :=
  splitOnCharAux delimiter cs []

def digitValue (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else
  if c = '2' then some 2 else if c = '3' then some 3 else
  if c = '4' then some 4 else if c = '5' then some 5 else
  if c = '6' then some 6 else if c = '7' then some 7 else
  if c = '8' then some 8 else if c = '9' then some 9 else none

def digitChar (n : Nat) : Char :=
  match n with
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | _ => '0'

def parseNatAux : Nat → List Char → Option Nat
  | n, [] => some n
  | n, c :: cs =>
      match digitValue c with
      | some d => parseNatAux (10 * n + d) cs
      | none => none

def parseNat (cs : List Char) : Option Nat :=
  match cs with
  | [] => none
  | _ => parseNatAux 0 cs

def natText (n : Nat) : List Char := (Nat.repr n).toList

def fileChar (f : Fin 8) : Char :=
  match f.val with
  | 0 => 'a'
  | 1 => 'b'
  | 2 => 'c'
  | 3 => 'd'
  | 4 => 'e'
  | 5 => 'f'
  | 6 => 'g'
  | 7 => 'h'
  | _ => 'a'

def rankChar (r : Fin 8) : Char :=
  match r.val with
  | 0 => '1'
  | 1 => '2'
  | 2 => '3'
  | 3 => '4'
  | 4 => '5'
  | 5 => '6'
  | 6 => '7'
  | 7 => '8'
  | _ => '1'

def fileOfChar (c : Char) : Option (Fin 8) :=
  if c = 'a' then some 0 else if c = 'b' then some 1 else
  if c = 'c' then some 2 else if c = 'd' then some 3 else
  if c = 'e' then some 4 else if c = 'f' then some 5 else
  if c = 'g' then some 6 else if c = 'h' then some 7 else none

def rankOfChar (c : Char) : Option (Fin 8) :=
  if c = '1' then some 0 else if c = '2' then some 1 else
  if c = '3' then some 2 else if c = '4' then some 3 else
  if c = '5' then some 4 else if c = '6' then some 5 else
  if c = '7' then some 6 else if c = '8' then some 7 else none

def squareText (s : Square) : List Char := [fileChar s.1, rankChar s.2]

def squareOfText : List Char → Option Square
  | [f, r] =>
      match fileOfChar f, rankOfChar r with
      | some f', some r' => some (f', r')
      | _, _ => none
  | _ => none

def pieceChar (q : Piece) : Char :=
  match q.color, q.kind with
  | .white, .king => 'K'
  | .white, .queen => 'Q'
  | .white, .rook => 'R'
  | .white, .bishop => 'B'
  | .white, .knight => 'N'
  | .white, .pawn => 'P'
  | .black, .king => 'k'
  | .black, .queen => 'q'
  | .black, .rook => 'r'
  | .black, .bishop => 'b'
  | .black, .knight => 'n'
  | .black, .pawn => 'p'

def pieceOfChar (c : Char) : Option Piece :=
  if c = 'K' then some ⟨.white, .king⟩ else
  if c = 'Q' then some ⟨.white, .queen⟩ else
  if c = 'R' then some ⟨.white, .rook⟩ else
  if c = 'B' then some ⟨.white, .bishop⟩ else
  if c = 'N' then some ⟨.white, .knight⟩ else
  if c = 'P' then some ⟨.white, .pawn⟩ else
  if c = 'k' then some ⟨.black, .king⟩ else
  if c = 'q' then some ⟨.black, .queen⟩ else
  if c = 'r' then some ⟨.black, .rook⟩ else
  if c = 'b' then some ⟨.black, .bishop⟩ else
  if c = 'n' then some ⟨.black, .knight⟩ else
  if c = 'p' then some ⟨.black, .pawn⟩ else none

def expandRank : List Char → Option (List (Option Piece))
  | [] => some []
  | c :: cs =>
      match pieceOfChar c with
      | some q => (expandRank cs).map (fun xs => some q :: xs)
      | none =>
          match digitValue c with
          | some n =>
              if 1 ≤ n ∧ n ≤ 8 then
                (expandRank cs).map (fun xs => List.replicate n none ++ xs)
              else none
          | none => none

def parseRank (cs : List Char) : Option (List (Option Piece)) :=
  match expandRank cs with
  | some xs => if xs.length = 8 then some xs else none
  | none => none

def allFenRanks : List (Fin 8) :=
  [⟨7, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩,
    ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩,
    ⟨1, by decide⟩, ⟨0, by decide⟩]

def updateRow : Board → Fin 8 → List (Fin 8) → List (Option Piece) → Board
  | b, _, _, [] => b
  | b, r, f :: fs, x :: xs => updateRow (boardUpdate b (f, r) x) r fs xs
  | b, _, _, _ => b

def updateRows : Board → List (Fin 8) → List (List Char) → Option Board
  | b, [], [] => some b
  | b, r :: rs, row :: rows =>
      match parseRank row with
      | some cells => updateRows (updateRow b r allFiles cells) rs rows
      | none => none
  | _, _, _ => none

def emptyBoard : Board := fun _ => none

def parsePlacement (cs : List Char) : Option Board :=
  updateRows emptyBoard allFenRanks (splitOnChar '/' cs)

def castleRightOfChar (c : Char) : Option CastleRight :=
  if c = 'K' then some .whiteKingSide else
  if c = 'Q' then some .whiteQueenSide else
  if c = 'k' then some .blackKingSide else
  if c = 'q' then some .blackQueenSide else none

def parseCastlingChars : List Char → Option (Finset CastleRight)
  | [] => some ∅
  | c :: cs =>
      match castleRightOfChar c, parseCastlingChars cs with
      | some r, some rs => if r ∈ rs then none else some (insert r rs)
      | _, _ => none

def parseCastling (cs : List Char) : Option (Finset CastleRight) :=
  match cs with
  | ['-'] => some ∅
  | [] => none
  | _ => parseCastlingChars cs

def castlingText (rights : Finset CastleRight) : List Char :=
  if rights = ∅ then ['-'] else
    (if .whiteKingSide ∈ rights then ['K'] else []) ++
    (if .whiteQueenSide ∈ rights then ['Q'] else []) ++
    (if .blackKingSide ∈ rights then ['k'] else []) ++
    (if .blackQueenSide ∈ rights then ['q'] else [])

def turnText : Color → List Char
  | .white => ['w']
  | .black => ['b']

def parseTurn : List Char → Option Color
  | ['w'] => some .white
  | ['b'] => some .black
  | _ => none

def enPassantText : Option Square → List Char
  | none => ['-']
  | some s => squareText s

def parseEnPassant : List Char → Option (Option Square)
  | ['-'] => some none
  | cs => (squareOfText cs).map some

def flushEmpty : Nat → List Char
  | 0 => []
  | 1 => ['1']
  | 2 => ['2']
  | 3 => ['3']
  | 4 => ['4']
  | 5 => ['5']
  | 6 => ['6']
  | 7 => ['7']
  | 8 => ['8']
  | _ => ['8']

def encodeCells : List (Option Piece) → Nat → List Char
  | [], n => flushEmpty n
  | none :: xs, n => encodeCells xs (n + 1)
  | some q :: xs, n => flushEmpty n ++ [pieceChar q] ++ encodeCells xs 0

def rankText (b : Board) (r : Fin 8) : List Char :=
  encodeCells (allFiles.map (fun f => b (f, r))) 0

def joinChar (delimiter : Char) : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: xs => x ++ [delimiter] ++ joinChar delimiter xs

def placementText (b : Board) : List Char :=
  joinChar '/' (allFenRanks.map (rankText b))

def printFen (p : Position) : String :=
  String.ofList <|
    joinChar ' '
      [placementText p.board, turnText p.turn, castlingText p.castling,
        enPassantText p.enPassant, natText p.halfmove, natText p.fullmove]

def parseFen (text : String) : Option Position :=
  match splitOnChar ' ' text.toList with
  | [placement, turn, castling, ep, halfmove, fullmove] =>
      match parsePlacement placement, parseTurn turn, parseCastling castling,
          parseEnPassant ep, parseNat halfmove, parseNat fullmove with
      | some b, some c, some rights, some ep', some hm, some fm =>
          if fm = 0 then none
          else some
            { board := b
              turn := c
              castling := rights
              enPassant := ep'
              halfmove := hm
              fullmove := fm }
      | _, _, _, _, _, _ => none
  | _ => none

def fenTextWellFormed (s : String) : Prop := parseFen s ≠ none

theorem pieceOfChar_pieceChar (q : Piece) : pieceOfChar (pieceChar q) = some q := by
  cases q with
  | mk c k => cases c <;> cases k <;> simp [pieceOfChar, pieceChar]

theorem fileOfChar_fileChar (f : Fin 8) : fileOfChar (fileChar f) = some f := by
  fin_cases f <;> simp [fileOfChar, fileChar]

theorem rankOfChar_rankChar (r : Fin 8) : rankOfChar (rankChar r) = some r := by
  fin_cases r <;> simp [rankOfChar, rankChar]

theorem parseTurn_turnText (c : Color) : parseTurn (turnText c) = some c := by
  cases c <;> rfl

theorem parseEnPassant_enPassantText (ep : Option Square) :
    parseEnPassant (enPassantText ep) = some ep := by
  cases ep with
  | none => rfl
  | some s =>
      cases s with
      | mk f r => simp [enPassantText, squareText, squareOfText,
          parseEnPassant, fileOfChar_fileChar, rankOfChar_rankChar]

theorem parseFenFields_printFenFields_text (p : Position) :
    parseFenFields (printFenFields p) = some p :=
  parseFenFields_printFenFields p

end Chess
