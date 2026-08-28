import Chess.Notation
import Chess.Game

/-!
# Canonical Standard Algebraic Notation

Printing is position-dependent: legal alternatives determine the minimum
source disambiguation, and the child position determines `+` versus `#`.
Parsing resolves only canonical strings against the verified legal-move list.
-/

namespace Chess

abbrev San := String

def sanPieceText : PieceKind → List Char
  | .king => ['K']
  | .queen => ['Q']
  | .rook => ['R']
  | .bishop => ['B']
  | .knight => ['N']
  | .pawn => []

def sanPromotionText : PromotionKind → List Char
  | .queen => ['Q']
  | .rook => ['R']
  | .bishop => ['B']
  | .knight => ['N']

def sanSamePieceB (p : Position) (m n : Move) : Bool :=
  match p.board m.source, p.board n.source with
  | some q, some q' =>
      (q.color == q'.color) && (q.kind == q'.kind) && (q.kind != .pawn)
  | _, _ => false

def sanSamePiece (p : Position) (m n : Move) : Prop := sanSamePieceB p m n = true

def sanCompetingMoves (p : Position) (m : Move) : List Move :=
  (legalMoves p).filter (fun n =>
    (n != m) && (!n.isCastle) && (n.destination == m.destination) &&
      sanSamePieceB p m n)

def sanFileConflictB (p : Position) (m : Move) : Bool :=
  (sanCompetingMoves p m).any (fun n => n.source.1 == m.source.1)

def sanFileConflict (p : Position) (m : Move) : Prop :=
  sanFileConflictB p m = true

def sanRankConflictB (p : Position) (m : Move) : Bool :=
  (sanCompetingMoves p m).any (fun n => n.source.2 == m.source.2)

def sanRankConflict (p : Position) (m : Move) : Prop :=
  sanRankConflictB p m = true

def sanDisambiguationText (p : Position) (m : Move) : List Char :=
  match p.board m.source with
  | some q =>
      if q.kind = .pawn then []
      else if (sanCompetingMoves p m).isEmpty then []
      else if !sanFileConflictB p m then [fileChar m.source.1]
      else if !sanRankConflictB p m then [rankChar m.source.2]
      else [fileChar m.source.1, rankChar m.source.2]
  | none => []

def sanCaptureText (p : Position) (m : Move) : List Char :=
  if moveIsCapture p m then ['x'] else []

def sanDestinationText (m : Move) : List Char := squareText m.destination

def sanPawnPrefix (p : Position) (m : Move) : List Char :=
  match p.board m.source with
  | some q => if q.kind = .pawn && moveIsCapture p m then [fileChar m.source.1] else []
  | none => []

def sanPromotionSuffix (m : Move) : List Char :=
  match m.promotionKind with
  | some k => ['=', (sanPromotionText k).head!]
  | none => []

def sanCheckSuffix (p : Position) (m : Move) : List Char :=
  let q := applyMove p m
  if checkmateB q then ['#']
  else if inCheckB q (Color.opposite p.turn) then ['+']
  else []

def sanNonCastleText (p : Position) (m : Move) : List Char :=
  match p.board m.source with
  | some q =>
      sanPieceText q.kind ++ sanPawnPrefix p m ++ sanDisambiguationText p m ++
        sanCaptureText p m ++ sanDestinationText m ++ sanPromotionSuffix m
  | none => []

def printSan (p : Position) (m : Move) : San :=
  String.ofList <|
    match m with
    | .whiteKingCastle | .blackKingCastle => ['O', '-', 'O'] ++ sanCheckSuffix p m
    | .whiteQueenCastle | .blackQueenCastle =>
        ['O', '-', 'O', '-', 'O'] ++ sanCheckSuffix p m
    | _ => sanNonCastleText p m ++ sanCheckSuffix p m

def sanWithoutCheck (s : San) : String :=
  String.ofList (s.toList.filter (fun c => c != '+' && c != '#'))

def parseSanMove (p : Position) (s : San) : Option Move :=
  (legalMoves p).find? (fun m => decide (printSan p m = s))

def sanDisambiguation (p : Position) (m : Move) : Finset Square :=
  (sanCompetingMoves p m).foldl (fun acc n => insert n.source acc) ∅

def sanUniqueOnLegalMovesB (p : Position) : Bool :=
  decide ((legalMoves p).map (printSan p)).Nodup

def sanUniqueOnLegalMoves (p : Position) : Prop :=
  sanUniqueOnLegalMovesB p = true

theorem sanPieceText_injective {a b : PieceKind}
    (h : sanPieceText a = sanPieceText b) : a = b := by
  cases a <;> cases b <;> simp [sanPieceText] at h ⊢

theorem sanPromotionText_injective {a b : PromotionKind}
    (h : sanPromotionText a = sanPromotionText b) : a = b := by
  cases a <;> cases b <;> simp [sanPromotionText] at h ⊢

theorem findSan_of_mem_unique {α : Type} (pred : α → Bool) (xs : List α) (x : α)
    (hmem : x ∈ xs) (hpred : pred x = true)
    (hunique : ∀ y, y ∈ xs → pred y = true → y = x) :
    xs.find? pred = some x := by
  induction xs with
  | nil => simp at hmem
  | cons y ys ih =>
      cases hpy : pred y with
      | true =>
          have hy : pred y = true := hpy
          have hyx : y = x := hunique y (by simp) hy
          have hpyx : pred x = true := by simpa [hyx] using hpy
          simp [List.find?, hyx, hpyx]
      | false =>
          have hy : ¬ pred y = true := by simp [hpy]
          have hxy : x ∈ ys := by
            rcases (List.mem_cons.mp hmem) with hxy | hxy
            · have : pred y = true := by simpa [hxy] using hpred
              exact False.elim (hy this)
            · exact hxy
          have htail : ∀ z, z ∈ ys → pred z = true → z = x := by
            intro z hz hzpred
            exact hunique z (by simp [hz]) hzpred
          simp [List.find?, hpy, ih hxy htail]

theorem parseSan_printSan_of_unique {p : Position} {m : Move}
    (hm : m ∈ legalMoves p)
    (hu : ∀ n, n ∈ legalMoves p → printSan p n = printSan p m → n = m) :
    parseSanMove p (printSan p m) = some m := by
  apply findSan_of_mem_unique
    (pred := fun n => decide (printSan p n = printSan p m))
  · exact hm
  · simp
  · intro n hn hprint
    exact hu n hn (by simpa using hprint)

theorem san_initial_e2e4 :
    printSan initialPosition
      (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩)) = "e4" := by
  native_decide

theorem san_initial_e2e4_parse :
    parseSanMove initialPosition "e4" =
      some (.normal (⟨4, by decide⟩, ⟨1, by decide⟩)
        (⟨4, by decide⟩, ⟨3, by decide⟩)) := by
  native_decide

theorem san_initial_unique : sanUniqueOnLegalMoves initialPosition := by
  change sanUniqueOnLegalMovesB initialPosition = true
  native_decide

end Chess
