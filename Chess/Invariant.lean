import Chess.History

/-!
# Reachability invariants

This module proves structural invariants of the orthodox transition system.
The proof is independent of the certificate checker: it analyzes each move
constructor, the finite board updates, and the castling-rights bookkeeping,
then lifts preservation through reflexive-transitive reachability.
-/

namespace Chess

theorem invariant_positionInvariant_initial : positionInvariant initialPosition := by
  unfold positionInvariant exactlyOneKing pawnOnPromotionRank rightsConsistent
  constructor
  · decide
  constructor
  · decide
  constructor
  · rintro ⟨⟨f, r⟩, c, hr, hpiece⟩
    fin_cases f <;> fin_cases r <;>
      simp [hasPiece, initialPosition, initialPiece, backRank] at hr hpiece
  constructor
  · intro r hr
    fin_cases r <;> simp [initialPosition, rightsConsistent, hasPiece,
      rightKingSquare, rightRookSquare, rightColor, initialPiece, backRank] at hr ⊢
  · decide

theorem invariant_boardMove_king_set (p : Position) (c : Color) (s t : Square)
    (hs : s ≠ t) (hsource : p.board s = some ⟨c, .king⟩)
    (hdest : p.board t ≠ some ⟨c, .king⟩) :
    squaresOf (boardMove p.board s t) c .king =
      (squaresOf p.board c .king \ {s}) ∪ ({t} : Finset Square) := by
  ext u
  by_cases hut : u = t
  · subst u
    simp [squaresOf, boardMove, boardUpdate, hs, hsource]
  · by_cases hus : u = s
    · subst u
      simp [squaresOf, boardMove, boardUpdate, hs, hsource]
    · simp [squaresOf, boardMove, boardUpdate, hus, hut]

theorem invariant_exactlyOneKing_boardMove (b : Board) (c : Color) (s t : Square)
    (hst : s ≠ t) (hK : exactlyOneKing b c)
    (ht : ¬ hasPiece b t c .king) :
    exactlyOneKing (boardMove b s t) c := by
  rcases (Finset.card_eq_one.mp hK) with ⟨k, hk⟩
  have hku (u : Square) : b u = some ⟨c, .king⟩ ↔ u = k := by
    have hu : u ∈ squaresOf b c .king ↔ u ∈ ({k} : Finset Square) := by
      rw [hk]
    simpa [squaresOf] using hu
  apply Finset.card_eq_one.mpr
  by_cases hks : k = s
  · refine ⟨t, ?_⟩
    ext u
    by_cases hut : u = t
    · subst u
      have hsource : b s = some ⟨c, .king⟩ := (hku s).2 (by simpa [hks])
      simp [squaresOf, boardMove, boardUpdate, hst, hsource]
    · by_cases hus : u = s
      · subst u
        simp [squaresOf, boardMove, boardUpdate, hst]
      · simp [squaresOf, boardMove, boardUpdate, hus, hut, hku, hks]
  · refine ⟨k, ?_⟩
    have hsk : s ≠ k := fun h => hks h.symm
    have htk : t ≠ k := by
      intro h
      exact ht ((hku t).2 h)
    ext u
    by_cases hus : u = s
    · subst u
      simp [squaresOf, boardMove, boardUpdate, hst, hsk, hku]
    · by_cases hut : u = t
      · subst u
        simp [squaresOf, boardMove, boardUpdate, hst, hsk, htk, hku]
      · simp [squaresOf, boardMove, boardUpdate, hus, hut, hku, hsk]

theorem invariant_exactlyOneKing_boardUpdate_unchanged (b : Board) (c : Color)
    (s : Square) (v : Option Piece) (hK : exactlyOneKing b c)
    (hs : ¬ hasPiece b s c .king)
    (hs' : ¬ hasPiece (boardUpdate b s v) s c .king) :
    exactlyOneKing (boardUpdate b s v) c := by
  rcases (Finset.card_eq_one.mp hK) with ⟨k, hk⟩
  have hku (u : Square) : b u = some ⟨c, .king⟩ ↔ u = k := by
    have hu : u ∈ squaresOf b c .king ↔ u ∈ ({k} : Finset Square) := by
      rw [hk]
    simpa [squaresOf] using hu
  have hsk : s ≠ k := by
    intro h
    exact hs ((hku s).2 h)
  apply Finset.card_eq_one.mpr
  refine ⟨k, ?_⟩
  ext u
  by_cases hus : u = s
  · subst u
    have hv : v ≠ some ⟨c, .king⟩ := by
      intro hv
      apply hs'
      simp [hasPiece, boardUpdate, hv]
    simp [squaresOf, boardUpdate, hsk, hv]
  · simp [squaresOf, boardUpdate, hus, hku]

theorem invariant_exactlyOneKing_two_updates (b : Board) (c : Color)
    (s t : Square) (v : Option Piece) (hK : exactlyOneKing b c)
    (hs : ¬ hasPiece b s c .king)
    (hs' : ¬ hasPiece (boardUpdate b s none) s c .king)
    (ht : ¬ hasPiece (boardUpdate b s none) t c .king)
    (ht' : ¬ hasPiece (boardUpdate (boardUpdate b s none) t v) t c .king) :
    exactlyOneKing (boardUpdate (boardUpdate b s none) t v) c := by
  exact invariant_exactlyOneKing_boardUpdate_unchanged
    (boardUpdate b s none) c t v
    (invariant_exactlyOneKing_boardUpdate_unchanged b c s none hK hs hs') ht ht'

theorem invariant_noPawnRank_boardMove (b : Board) (s t : Square)
    (hst : s ≠ t) (hno : ¬ pawnOnPromotionRank b)
    (htpawn : ∀ c, b s = some ⟨c, .pawn⟩ →
      ¬ (t.2.val = 0 ∨ t.2.val = 7)) :
    ¬ pawnOnPromotionRank (boardMove b s t) := by
  rintro ⟨u, c, hurank, hu⟩
  by_cases hut : u = t
  · subst u
    have hsource : b s = some ⟨c, .pawn⟩ := by
      simpa [hasPiece, boardMove, boardUpdate, hst] using hu
    exact htpawn c hsource hurank
  · by_cases hus : u = s
    · subst u
      simp [hasPiece, boardMove, boardUpdate, hst] at hu
    · apply hno
      exact ⟨u, c, hurank, by simpa [hasPiece, boardMove, boardUpdate, hus, hut] using hu⟩

theorem invariant_noPawnRank_boardUpdate (b : Board) (s : Square) (v : Option Piece)
    (hno : ¬ pawnOnPromotionRank b)
    (hv : ∀ c, v ≠ some ⟨c, .pawn⟩) :
    ¬ pawnOnPromotionRank (boardUpdate b s v) := by
  rintro ⟨u, c, hurank, hu⟩
  by_cases hus : u = s
  · subst u
    exact hv c (by simpa [hasPiece, boardUpdate] using hu)
  · apply hno
    exact ⟨u, c, hurank, by simpa [hasPiece, boardUpdate, hus] using hu⟩

theorem invariant_pawn_geometry_target_not_extreme (c : Color) (s t : Square)
    (hsrc : ¬ (s.2.val = 0 ∨ s.2.val = 7))
    (htarget : t.2 ≠ promotionRank c)
    (hgeom : pawnMoveGeometryB c s t = true ∨
      pawnAttackGeometryB c s t = true ∨ pawnDoubleGeometryB c s t = true) :
    ¬ (t.2.val = 0 ∨ t.2.val = 7) := by
  rcases s with ⟨sf, sr⟩
  rcases t with ⟨tf, tr⟩
  cases c <;> fin_cases sr <;> fin_cases tr <;>
    simp [promotionRank, pawnMoveGeometryB, pawnAttackGeometryB,
      pawnDoubleGeometryB] at hsrc htarget hgeom ⊢

theorem invariant_normal_pseudo_facts (p : Position) (s t : Square)
    (h : normalPseudoLegal p s t) :
    s ≠ t ∧ ∀ c, ¬ hasPiece p.board t c .king := by
  constructor
  · intro hst
    subst t
    cases hsrc : p.board s with
    | none => simp [normalPseudoLegal, normalPseudoLegalB, hsrc] at h
    | some q =>
        cases q with
        | mk qc qk =>
            cases qc <;> cases qk <;>
              simp [normalPseudoLegal, normalPseudoLegalB, hsrc,
                normalPieceGeometryB, pawnMoveGeometryB, pawnAttackGeometryB,
                pawnDoubleGeometryB, rookGeometryB, bishopGeometryB,
                queenGeometryB, knightGeometryB, kingGeometryB,
                sameDiagonalB, absDiff] at h
  · intro c ht
    change p.board t = some ⟨c, .king⟩ at ht
    have hdest : destinationFriendlyB p p.turn t = true := by
      cases hsrc : p.board s with
      | none => simp [normalPseudoLegal, normalPseudoLegalB, hsrc] at h
      | some q =>
          have hparts : (q.color == p.turn) = true ∧
              destinationFriendlyB p p.turn t = true ∧
              ((q.kind != .pawn) || (t.2 != promotionRank p.turn)) = true ∧
              normalPieceGeometryB p p.turn q s t = true := by
            simpa only [normalPseudoLegal, normalPseudoLegalB, hsrc,
              Bool.and_eq_true, and_assoc] using h
          exact hparts.2.1
    simp [destinationFriendlyB, ht] at hdest

theorem invariant_normal_pawn_target_not_extreme (p : Position) (s t : Square)
    (h : normalPseudoLegal p s t) (hno : ¬ pawnOnPromotionRank p.board) :
    ∀ c, p.board s = some ⟨c, .pawn⟩ →
      ¬ (t.2.val = 0 ∨ t.2.val = 7) := by
  intro c hsource
  cases hsrc : p.board s with
  | none => simp [hsrc] at hsource
  | some q =>
      have hq : q = ⟨c, .pawn⟩ := by simpa [hsrc] using hsource
      subst q
      have hsrcNo : ¬ (s.2.val = 0 ∨ s.2.val = 7) := by
        intro hr
        apply hno
        exact ⟨s, c, hr, by simpa [hsrc]⟩
      have hparts : (c == p.turn) = true ∧
          destinationFriendlyB p p.turn t = true ∧
          ((PieceKind.pawn != .pawn) || (t.2 != promotionRank p.turn)) = true ∧
          normalPieceGeometryB p p.turn ⟨c, .pawn⟩ s t = true := by
        simpa only [normalPseudoLegal, normalPseudoLegalB, hsrc,
          Bool.and_eq_true, and_assoc] using h
      rcases hparts with ⟨hcolor, hdest, hpromo, hgeom⟩
      have hturn : c = p.turn := by simpa using hcolor
      have htarget : t.2 ≠ promotionRank c := by
        simpa [hturn] using hpromo
      simp only [normalPieceGeometryB, Bool.or_eq_true, Bool.and_eq_true] at hgeom
      have hgeom : pawnMoveGeometryB c s t = true ∨
          pawnAttackGeometryB c s t = true ∨ pawnDoubleGeometryB c s t = true := by
        rcases hgeom with hma | hd
        · rcases hma with hm | ha
          · exact Or.inl (by simpa [hturn] using hm.1)
          · exact Or.inr (Or.inl (by simpa [hturn] using ha.1))
        · exact Or.inr (Or.inr (by simpa [hturn] using hd.1.1))
      exact invariant_pawn_geometry_target_not_extreme c s t hsrcNo htarget hgeom

theorem invariant_normal_preserves_king_count (p : Position) (s t : Square)
    (h : normalPseudoLegal p s t) (c : Color)
    (hK : exactlyOneKing p.board c) :
    exactlyOneKing (boardMove p.board s t) c := by
  have hf := invariant_normal_pseudo_facts p s t h
  exact invariant_exactlyOneKing_boardMove p.board c s t hf.1 hK (hf.2 c)

theorem invariant_normal_preserves_pawn_rank (p : Position) (s t : Square)
    (h : normalPseudoLegal p s t) (hno : ¬ pawnOnPromotionRank p.board) :
    ¬ pawnOnPromotionRank (boardMove p.board s t) := by
  have hf := invariant_normal_pseudo_facts p s t h
  exact invariant_noPawnRank_boardMove p.board s t hf.1 hno
    (invariant_normal_pawn_target_not_extreme p s t h hno)

theorem invariant_promotion_source_not_king (p : Position) (s t : Square)
    (k : PromotionKind) (h : pseudoLegalPromotion p (.promotion s t k))
    (c : Color) : ¬ hasPiece p.board s c .king := by
  intro hs
  cases hsrc : p.board s with
  | none => simp [hasPiece, hsrc] at hs
  | some q =>
      have hq : q = ⟨c, .king⟩ := by simpa [hasPiece, hsrc] using hs
      subst q
      simp [pseudoLegalPromotion, pseudoLegalPromotionB, hsrc] at h

theorem invariant_promotion_target_not_king (p : Position) (s t : Square)
    (k : PromotionKind) (h : pseudoLegalPromotion p (.promotion s t k))
    (c : Color) :
    ¬ hasPiece (boardUpdate p.board s none) t c .king := by
  intro ht
  by_cases hst : s = t
  · subst t
    simp [hasPiece, boardUpdate] at ht
  · have htold : p.board t = some ⟨c, .king⟩ := by
      have hts : t ≠ s := Ne.symm hst
      simpa [hasPiece, boardUpdate, hts] using ht
    cases hsrc : p.board s with
    | none => simp [pseudoLegalPromotion, pseudoLegalPromotionB, hsrc] at h
    | some q =>
        simp [pseudoLegalPromotion, pseudoLegalPromotionB, hsrc, htold] at h

theorem invariant_promotion_final_target_not_king (p : Position) (s t : Square)
    (k : PromotionKind) (c : Color) :
    ¬ hasPiece
      (boardUpdate (boardUpdate p.board s none) t
        (some ⟨p.turn, k.toPieceKind⟩)) t c .king := by
  intro ht
  by_cases hst : s = t
  · subst t
    cases c <;> cases k <;>
      simp [hasPiece, boardUpdate, PromotionKind.toPieceKind] at ht
  · cases c <;> cases k <;>
      simp [hasPiece, boardUpdate, hst, PromotionKind.toPieceKind] at ht

theorem invariant_promotion_preserves_king_count (p : Position) (s t : Square)
    (k : PromotionKind) (h : pseudoLegalPromotion p (.promotion s t k))
    (c : Color) (hK : exactlyOneKing p.board c) :
    exactlyOneKing
      (boardUpdate (boardUpdate p.board s none) t
        (some ⟨p.turn, k.toPieceKind⟩)) c := by
  exact invariant_exactlyOneKing_two_updates p.board c s t
    (some ⟨p.turn, k.toPieceKind⟩) hK
    (invariant_promotion_source_not_king p s t k h c)
    (by simp [hasPiece, boardUpdate])
    (invariant_promotion_target_not_king p s t k h c)
    (invariant_promotion_final_target_not_king p s t k c)

theorem invariant_promotion_preserves_pawn_rank (p : Position) (s t : Square)
    (k : PromotionKind) (hno : ¬ pawnOnPromotionRank p.board) :
    ¬ pawnOnPromotionRank
      (boardUpdate (boardUpdate p.board s none) t
        (some ⟨p.turn, k.toPieceKind⟩)) := by
  apply invariant_noPawnRank_boardUpdate
    (boardUpdate p.board s none) t (some ⟨p.turn, k.toPieceKind⟩)
    (invariant_noPawnRank_boardUpdate p.board s none hno (by simp))
  intro c
  cases k <;> simp [PromotionKind.toPieceKind]

theorem invariant_en_passant_facts (p : Position) (s t : Square)
    (h : pseudoLegalEnPassant p (.enPassant s t)) :
    s ≠ t ∧ p.board t = none ∧
      pawnAttackGeometryB p.turn s t = true ∧
      ∃ cs, epCapturedSquare p.turn t = some cs ∧
        p.board cs = some ⟨p.turn.opposite, .pawn⟩ := by
  cases hep : p.enPassant with
  | none => simp [pseudoLegalEnPassant, pseudoLegalEnPassantB, hep] at h
  | some ep =>
      cases hsrc : p.board s with
      | none => simp [pseudoLegalEnPassant, pseudoLegalEnPassantB, hep, hsrc] at h
      | some q =>
          simp only [pseudoLegalEnPassant, pseudoLegalEnPassantB, hep, hsrc,
            Bool.and_eq_true, and_assoc] at h
          rcases h with ⟨hepT, hcolor, hkind, hgeom, ht, hcap⟩
          have hne : s ≠ t := by
            intro hst
            subst t
            simp [pawnAttackGeometryB, absDiff] at hgeom
          have ht' : p.board t = none := by simpa using ht
          have hcs : ∃ cs, epCapturedSquare p.turn t = some cs ∧
              p.board cs = some ⟨p.turn.opposite, .pawn⟩ := by
            cases hcs : epCapturedSquare p.turn t with
            | none => simp [hcs] at hcap
            | some cs =>
                refine ⟨cs, rfl, ?_⟩
                simpa [hcs] using hcap
          exact ⟨hne, ht', hgeom, hcs⟩

theorem invariant_absDiff_one_ne (a b : Fin 8) (h : absDiff a b = 1) : a ≠ b := by
  intro hab
  subst b
  simp [absDiff] at h

theorem invariant_en_passant_captured_square_distinct (p : Position)
    (s t cs : Square)
    (hcs : epCapturedSquare p.turn t = some cs)
    (hgeom : pawnAttackGeometryB p.turn s t = true) :
    cs ≠ s ∧ cs ≠ t := by
  rcases s with ⟨sf, sr⟩
  rcases t with ⟨tf, tr⟩
  rcases cs with ⟨cf, cr⟩
  cases hturn : p.turn <;>
    fin_cases sr <;> fin_cases tr <;> fin_cases cr <;>
      simp [epCapturedSquare, pawnAttackGeometryB, hturn] at hcs hgeom ⊢ <;>
        try
          (intro hcf
           apply invariant_absDiff_one_ne sf tf hgeom
           exact (hcs.trans hcf).symm)

theorem invariant_en_passant_preserves_king_count (p : Position) (s t : Square)
    (h : pseudoLegalEnPassant p (.enPassant s t)) (c : Color)
    (hK : exactlyOneKing p.board c) :
    ∃ cs, epCapturedSquare p.turn t = some cs ∧
      exactlyOneKing (boardUpdate (boardMove p.board s t) cs none) c := by
  have hf := invariant_en_passant_facts p s t h
  rcases hf with ⟨hst, ht, hgeom, ⟨cs, hcs, hpiece⟩⟩
  have hdist := invariant_en_passant_captured_square_distinct p s t cs hcs hgeom
  have htking : ¬ hasPiece p.board t c .king := by
    simp [hasPiece, ht]
  have hfirst : exactlyOneKing (boardMove p.board s t) c :=
    invariant_exactlyOneKing_boardMove p.board c s t hst hK htking
  have hcsold : ¬ hasPiece (boardMove p.board s t) cs c .king := by
    intro hbad
    have hbad' : p.board cs = some ⟨c, .king⟩ := by
      simpa [hasPiece, boardMove, boardUpdate, hdist.1, hdist.2] using hbad
    have hneq : (some ⟨c, .king⟩ : Option Piece) ≠
        some ⟨p.turn.opposite, .pawn⟩ := by
      cases p.turn <;> cases c <;> simp
    exact hneq (hbad'.symm.trans hpiece)
  have hcsnew : ¬ hasPiece
      (boardUpdate (boardMove p.board s t) cs none) cs c .king := by
    simp [hasPiece, boardUpdate]
  refine ⟨cs, hcs, ?_⟩
  exact invariant_exactlyOneKing_boardUpdate_unchanged
    (boardMove p.board s t) c cs none hfirst hcsold hcsnew

theorem invariant_en_passant_target_not_extreme (p : Position) (s t : Square)
    (h : pseudoLegalEnPassant p (.enPassant s t)) :
    ¬ (t.2.val = 0 ∨ t.2.val = 7) := by
  have hf := invariant_en_passant_facts p s t h
  rcases hf.2.2.2 with ⟨cs, hcs, hpiece⟩
  rcases t with ⟨tf, tr⟩
  rcases cs with ⟨cf, cr⟩
  cases hturn : p.turn <;>
    fin_cases tr <;> fin_cases cr <;>
      simp [epCapturedSquare, hturn] at hcs ⊢

theorem invariant_en_passant_preserves_pawn_rank (p : Position) (s t : Square)
    (h : pseudoLegalEnPassant p (.enPassant s t))
    (hno : ¬ pawnOnPromotionRank p.board) :
    ∃ cs, epCapturedSquare p.turn t = some cs ∧
      ¬ pawnOnPromotionRank (boardUpdate (boardMove p.board s t) cs none) := by
  have hf := invariant_en_passant_facts p s t h
  rcases hf with ⟨hst, ht, hgeom, ⟨cs, hcs, hpiece⟩⟩
  have hmove : ¬ pawnOnPromotionRank (boardMove p.board s t) :=
    invariant_noPawnRank_boardMove p.board s t hst hno
      (fun c hs => invariant_en_passant_target_not_extreme p s t h)
  refine ⟨cs, hcs, ?_⟩
  exact invariant_noPawnRank_boardUpdate (boardMove p.board s t) cs none hmove (by simp)

theorem invariant_castle_board_preserves_king_count
    (b : Board) (c : Color) (ks kt rs rd : Square)
    (hK : exactlyOneKing b c) (hkskt : ks ≠ kt)
    (hkt : ¬ hasPiece b kt c .king)
    (hrsks : rs ≠ ks) (hrskt : rs ≠ kt)
    (hrdks : rd ≠ ks) (hrdkt : rd ≠ kt) (hrsrd : rs ≠ rd)
    (hrs : ¬ hasPiece b rs c .king)
    (hrd : ¬ hasPiece b rd c .king) :
    exactlyOneKing
      (boardUpdate (boardUpdate (boardMove b ks kt) rs none) rd (b rs)) c := by
  have hfirst : exactlyOneKing (boardMove b ks kt) c :=
    invariant_exactlyOneKing_boardMove b c ks kt hkskt hK hkt
  have hrs' : ¬ hasPiece (boardMove b ks kt) rs c .king := by
    intro hbad
    apply hrs
    simpa [hasPiece, boardMove, boardUpdate, hrsks, hrskt] using hbad
  have hrsnew : ¬ hasPiece (boardUpdate (boardMove b ks kt) rs none) rs c .king := by
    simp [hasPiece, boardUpdate]
  have hmid : exactlyOneKing (boardUpdate (boardMove b ks kt) rs none) c :=
    invariant_exactlyOneKing_boardUpdate_unchanged
      (boardMove b ks kt) c rs none hfirst hrs' hrsnew
  have hrd' : ¬ hasPiece (boardUpdate (boardMove b ks kt) rs none) rd c .king := by
    intro hbad
    apply hrd
    have hrds : rd ≠ rs := Ne.symm hrsrd
    simpa [hasPiece, boardMove, boardUpdate, hrdks, hrdkt, hrds] using hbad
  have hrdnew : ¬ hasPiece
      (boardUpdate (boardUpdate (boardMove b ks kt) rs none) rd (b rs))
      rd c .king := by
    intro hbad
    have hvalue : b rs = some ⟨c, .king⟩ := by
      simpa [hasPiece, boardUpdate] using hbad
    exact hrs (by simpa [hasPiece] using hvalue)
  exact invariant_exactlyOneKing_boardUpdate_unchanged
    (boardUpdate (boardMove b ks kt) rs none) c rd (b rs)
    hmid hrd' hrdnew

theorem invariant_castle_preserves_king_count (p : Position) (m : Move)
    (h : pseudoLegalCastle p m) (c : Color)
    (hK : exactlyOneKing p.board c) :
    exactlyOneKing (castleBoard p m) c := by
  cases m with
  | normal s t =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | promotion s t k =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | enPassant s t =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | whiteKingCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hF, hG⟩
      have hrds : ((⟨5, by decide⟩, ⟨0, by decide⟩) : Square) ≠
          (⟨7, by decide⟩, ⟨0, by decide⟩) := by decide
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination, boardMove, boardUpdate, hrds] using
        (invariant_castle_board_preserves_king_count p.board c
          (⟨4, by decide⟩, ⟨0, by decide⟩)
          (⟨6, by decide⟩, ⟨0, by decide⟩)
          (⟨7, by decide⟩, ⟨0, by decide⟩)
          (⟨5, by decide⟩, ⟨0, by decide⟩)
          hK (by decide) (by simp [hasPiece, hG])
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by simp [hasPiece, hrook]) (by simp [hasPiece, hF]))
  | whiteQueenCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hB, hC, hD⟩
      have hrds : ((⟨3, by decide⟩, ⟨0, by decide⟩) : Square) ≠
          (⟨0, by decide⟩, ⟨0, by decide⟩) := by decide
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination, boardMove, boardUpdate, hrds] using
        (invariant_castle_board_preserves_king_count p.board c
          (⟨4, by decide⟩, ⟨0, by decide⟩)
          (⟨2, by decide⟩, ⟨0, by decide⟩)
          (⟨0, by decide⟩, ⟨0, by decide⟩)
          (⟨3, by decide⟩, ⟨0, by decide⟩)
          hK (by decide) (by simp [hasPiece, hC])
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by simp [hasPiece, hrook]) (by simp [hasPiece, hD]))
  | blackKingCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hF, hG⟩
      have hrds : ((⟨5, by decide⟩, ⟨7, by decide⟩) : Square) ≠
          (⟨7, by decide⟩, ⟨7, by decide⟩) := by decide
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination, boardMove, boardUpdate, hrds] using
        (invariant_castle_board_preserves_king_count p.board c
          (⟨4, by decide⟩, ⟨7, by decide⟩)
          (⟨6, by decide⟩, ⟨7, by decide⟩)
          (⟨7, by decide⟩, ⟨7, by decide⟩)
          (⟨5, by decide⟩, ⟨7, by decide⟩)
          hK (by decide) (by simp [hasPiece, hG])
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by simp [hasPiece, hrook]) (by simp [hasPiece, hF]))
  | blackQueenCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hB, hC, hD⟩
      have hrds : ((⟨3, by decide⟩, ⟨7, by decide⟩) : Square) ≠
          (⟨0, by decide⟩, ⟨7, by decide⟩) := by decide
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination, boardMove, boardUpdate, hrds] using
        (invariant_castle_board_preserves_king_count p.board c
          (⟨4, by decide⟩, ⟨7, by decide⟩)
          (⟨2, by decide⟩, ⟨7, by decide⟩)
          (⟨0, by decide⟩, ⟨7, by decide⟩)
          (⟨3, by decide⟩, ⟨7, by decide⟩)
          hK (by decide) (by simp [hasPiece, hC])
          (by decide) (by decide) (by decide) (by decide) (by decide)
          (by simp [hasPiece, hrook]) (by simp [hasPiece, hD]))

theorem invariant_castle_board_preserves_pawn_rank
    (b : Board) (ks kt rs rd : Square)
    (hkskt : ks ≠ kt) (hrsks : rs ≠ ks) (hrskt : rs ≠ kt)
    (hrsrd : rs ≠ rd)
    (hks : ∀ c, b ks ≠ some ⟨c, .pawn⟩)
    (hrs : ∀ c, b rs ≠ some ⟨c, .pawn⟩)
    (hno : ¬ pawnOnPromotionRank b) :
    ¬ pawnOnPromotionRank (boardMove (boardMove b ks kt) rs rd) := by
  have hfirst : ¬ pawnOnPromotionRank (boardMove b ks kt) :=
    invariant_noPawnRank_boardMove b ks kt hkskt hno
      (fun c hs => False.elim (hks c hs))
  have hrs' : ∀ c, boardMove b ks kt rs ≠ some ⟨c, .pawn⟩ := by
    intro c hs
    apply hrs c
    simpa [boardMove, boardUpdate, hrskt, hrsks] using hs
  exact invariant_noPawnRank_boardMove (boardMove b ks kt) rs rd hrsrd hfirst
    (fun c hs => False.elim (hrs' c hs))

theorem invariant_castle_preserves_pawn_rank (p : Position) (m : Move)
    (h : pseudoLegalCastle p m) (hno : ¬ pawnOnPromotionRank p.board) :
    ¬ pawnOnPromotionRank (castleBoard p m) := by
  cases m with
  | normal s t =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | promotion s t k =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | enPassant s t =>
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleColorOf,
        castleRightOf, castleRookSource] at h
  | whiteKingCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hF, hG⟩
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination] using
        (invariant_castle_board_preserves_pawn_rank p.board
          (⟨4, by decide⟩, ⟨0, by decide⟩)
          (⟨6, by decide⟩, ⟨0, by decide⟩)
          (⟨7, by decide⟩, ⟨0, by decide⟩)
          (⟨5, by decide⟩, ⟨0, by decide⟩)
          (by decide) (by decide) (by decide) (by decide)
          (by intro c; simp [hking]) (by intro c; simp [hrook]) hno)
  | whiteQueenCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hB, hC, hD⟩
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination] using
        (invariant_castle_board_preserves_pawn_rank p.board
          (⟨4, by decide⟩, ⟨0, by decide⟩)
          (⟨2, by decide⟩, ⟨0, by decide⟩)
          (⟨0, by decide⟩, ⟨0, by decide⟩)
          (⟨3, by decide⟩, ⟨0, by decide⟩)
          (by decide) (by decide) (by decide) (by decide)
          (by intro c; simp [hking]) (by intro c; simp [hrook]) hno)
  | blackKingCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hF, hG⟩
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination] using
        (invariant_castle_board_preserves_pawn_rank p.board
          (⟨4, by decide⟩, ⟨7, by decide⟩)
          (⟨6, by decide⟩, ⟨7, by decide⟩)
          (⟨7, by decide⟩, ⟨7, by decide⟩)
          (⟨5, by decide⟩, ⟨7, by decide⟩)
          (by decide) (by decide) (by decide) (by decide)
          (by intro c; simp [hking]) (by intro c; simp [hrook]) hno)
  | blackQueenCastle =>
      have hp := h
      simp [pseudoLegalCastle, pseudoLegalCastleB, castleClearB,
        castleEmptySquares, castleColorOf, castleRightOf, castleRookSource,
        Bool.and_eq_true, and_assoc] at hp
      rcases hp with ⟨hturn, hright, hking, hrook, hB, hC, hD⟩
      simpa [castleBoard, castleRookSource, castleRookDestination,
        Move.source, Move.destination] using
        (invariant_castle_board_preserves_pawn_rank p.board
          (⟨4, by decide⟩, ⟨7, by decide⟩)
          (⟨2, by decide⟩, ⟨7, by decide⟩)
          (⟨0, by decide⟩, ⟨7, by decide⟩)
          (⟨3, by decide⟩, ⟨7, by decide⟩)
          (by decide) (by decide) (by decide) (by decide)
          (by intro c; simp [hking]) (by intro c; simp [hrook]) hno)

theorem invariant_pseudo_preserves_king_count (p : Position) (m : Move)
    (h : pseudoLegal p m) (c : Color)
    (hK : exactlyOneKing p.board c) :
    exactlyOneKing (applyBoard p m) c := by
  cases m with
  | normal s t =>
      have hn : normalPseudoLegal p s t := by
        simpa [pseudoLegal, pseudoLegalB, normalPseudoLegal] using h
      simpa [applyBoard] using invariant_normal_preserves_king_count p s t hn c hK
  | promotion s t k =>
      have hp : pseudoLegalPromotion p (.promotion s t k) := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalPromotion] using h
      simpa [applyBoard] using invariant_promotion_preserves_king_count p s t k hp c hK
  | enPassant s t =>
      have he : pseudoLegalEnPassant p (.enPassant s t) := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalEnPassant] using h
      rcases invariant_en_passant_preserves_king_count p s t he c hK with
        ⟨cs, hcs, hk⟩
      simpa [applyBoard, hcs] using hk
  | whiteKingCastle =>
      have hc : pseudoLegalCastle p .whiteKingCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_king_count p .whiteKingCastle hc c hK
  | whiteQueenCastle =>
      have hc : pseudoLegalCastle p .whiteQueenCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_king_count p .whiteQueenCastle hc c hK
  | blackKingCastle =>
      have hc : pseudoLegalCastle p .blackKingCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_king_count p .blackKingCastle hc c hK
  | blackQueenCastle =>
      have hc : pseudoLegalCastle p .blackQueenCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_king_count p .blackQueenCastle hc c hK

theorem invariant_pseudo_preserves_pawn_rank (p : Position) (m : Move)
    (h : pseudoLegal p m) (hno : ¬ pawnOnPromotionRank p.board) :
    ¬ pawnOnPromotionRank (applyBoard p m) := by
  cases m with
  | normal s t =>
      have hn : normalPseudoLegal p s t := by
        simpa [pseudoLegal, pseudoLegalB, normalPseudoLegal] using h
      simpa [applyBoard] using invariant_normal_preserves_pawn_rank p s t hn hno
  | promotion s t k =>
      simpa [applyBoard] using invariant_promotion_preserves_pawn_rank p s t k hno
  | enPassant s t =>
      have he : pseudoLegalEnPassant p (.enPassant s t) := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalEnPassant] using h
      rcases invariant_en_passant_preserves_pawn_rank p s t he hno with
        ⟨cs, hcs, hpawn⟩
      simpa [applyBoard, hcs] using hpawn
  | whiteKingCastle =>
      have hc : pseudoLegalCastle p .whiteKingCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_pawn_rank p .whiteKingCastle hc hno
  | whiteQueenCastle =>
      have hc : pseudoLegalCastle p .whiteQueenCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_pawn_rank p .whiteQueenCastle hc hno
  | blackKingCastle =>
      have hc : pseudoLegalCastle p .blackKingCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_pawn_rank p .blackKingCastle hc hno
  | blackQueenCastle =>
      have hc : pseudoLegalCastle p .blackQueenCastle := by
        simpa [pseudoLegal, pseudoLegalB, pseudoLegalCastle] using h
      simpa [applyBoard, castleBoard] using
        invariant_castle_preserves_pawn_rank p .blackQueenCastle hc hno

theorem invariant_right_home_preserved (p : Position) (m : Move) (r : CastleRight)
    (hr : r ∈ rightsAfterMove p m) :
    applyBoard p m (rightKingSquare r) = p.board (rightKingSquare r) ∧
      applyBoard p m (rightRookSquare r) = p.board (rightRookSquare r) := by
  have hnot : r ∉ rightsRemovedForMove p m := (Finset.mem_sdiff.mp hr).2
  have hnot_touched (u : Square)
      (hu : u ∈ ({m.source, m.destination} ∪
        match castleRookSource m, castleRookDestination m with
        | some rs, some rd => {rs, rd}
        | _, _ => (∅ : Finset Square))) : r ∉ rightsRemovedForSquare u := by
    intro hus
    apply hnot
    unfold rightsRemovedForMove
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨u, hu, hus⟩
  have hnot_capture (u : Square)
      (hu : moveCaptureSquare p m = some u) :
      r ∉ rightsRemovedForSquare u := by
    intro hus
    apply hnot
    unfold rightsRemovedForMove
    apply Finset.mem_union_right
    simp [hu, hus]
  have hking_not_removed (u : Square)
      (hu : r ∉ rightsRemovedForSquare u) : rightKingSquare r ≠ u := by
    intro heq
    apply hu
    simp [rightsRemovedForSquare, heq]
  have hrook_not_removed (u : Square)
      (hu : r ∉ rightsRemovedForSquare u) : rightRookSquare r ≠ u := by
    intro heq
    apply hu
    simp [rightsRemovedForSquare, heq]
  have hking_touched (u : Square)
      (hu : u ∈ ({m.source, m.destination} ∪
        match castleRookSource m, castleRookDestination m with
        | some rs, some rd => {rs, rd}
        | _, _ => (∅ : Finset Square))) : rightKingSquare r ≠ u :=
    hking_not_removed u (hnot_touched u hu)
  have hrook_touched (u : Square)
      (hu : u ∈ ({m.source, m.destination} ∪
        match castleRookSource m, castleRookDestination m with
        | some rs, some rd => {rs, rd}
        | _, _ => (∅ : Finset Square))) : rightRookSquare r ≠ u :=
    hrook_not_removed u (hnot_touched u hu)
  cases m with
  | normal s t =>
      have hks : rightKingSquare r ≠ s := hking_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hkt : rightKingSquare r ≠ t := hking_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrs : rightRookSquare r ≠ s := hrook_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrt : rightRookSquare r ≠ t := hrook_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      constructor <;> simp [applyBoard, boardMove, boardUpdate, hks, hkt, hrs, hrt]
  | promotion s t k =>
      have hks : rightKingSquare r ≠ s := hking_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hkt : rightKingSquare r ≠ t := hking_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrs : rightRookSquare r ≠ s := hrook_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrt : rightRookSquare r ≠ t := hrook_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      constructor <;> simp [applyBoard, boardUpdate, hks, hkt, hrs, hrt]
  | enPassant s t =>
      have hks : rightKingSquare r ≠ s := hking_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hkt : rightKingSquare r ≠ t := hking_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrs : rightRookSquare r ≠ s := hrook_touched s
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      have hrt : rightRookSquare r ≠ t := hrook_touched t
        (by simp [Move.source, Move.destination, castleRookSource, castleRookDestination])
      cases hec : epCapturedSquare p.turn t with
      | none =>
          constructor <;>
            simp [applyBoard, boardMove, boardUpdate, hec, hks, hkt, hrs, hrt]
      | some cs =>
          have hcap : r ∉ rightsRemovedForSquare cs := by
            apply hnot_capture cs
            simpa [moveCaptureSquare] using hec
          have hkc : rightKingSquare r ≠ cs := hking_not_removed cs hcap
          have hrc : rightRookSquare r ≠ cs := hrook_not_removed cs hcap
          constructor <;>
            simp [applyBoard, boardMove, boardUpdate, hec, hks, hkt, hrs, hrt,
              hkc, hrc]
  | whiteKingCastle =>
      have hks : rightKingSquare r ≠ (⟨4, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hkt : rightKingSquare r ≠ (⟨6, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrs : rightKingSquare r ≠ (⟨7, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrd : rightKingSquare r ≠ (⟨5, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rks : rightRookSquare r ≠ (⟨4, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rkt : rightRookSquare r ≠ (⟨6, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrs : rightRookSquare r ≠ (⟨7, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrd : rightRookSquare r ≠ (⟨5, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      constructor <;>
        simp only [applyBoard, castleBoard, boardMove, boardUpdate, Move.source,
          Move.destination, castleRookSource, castleRookDestination,
          Function.update_apply]
      all_goals split <;> simp_all
  | whiteQueenCastle =>
      have hks : rightKingSquare r ≠ (⟨4, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hkt : rightKingSquare r ≠ (⟨2, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrs : rightKingSquare r ≠ (⟨0, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrd : rightKingSquare r ≠ (⟨3, by decide⟩, ⟨0, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rks : rightRookSquare r ≠ (⟨4, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rkt : rightRookSquare r ≠ (⟨2, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrs : rightRookSquare r ≠ (⟨0, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrd : rightRookSquare r ≠ (⟨3, by decide⟩, ⟨0, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      constructor <;>
        simp_all [applyBoard, castleBoard, boardMove, boardUpdate, Move.source,
          Move.destination, castleRookSource, castleRookDestination,
          Function.update_apply,
          hks, hkt, hrs, hrd, rks, rkt, rrs, rrd]
  | blackKingCastle =>
      have hks : rightKingSquare r ≠ (⟨4, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hkt : rightKingSquare r ≠ (⟨6, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrs : rightKingSquare r ≠ (⟨7, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrd : rightKingSquare r ≠ (⟨5, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rks : rightRookSquare r ≠ (⟨4, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rkt : rightRookSquare r ≠ (⟨6, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrs : rightRookSquare r ≠ (⟨7, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrd : rightRookSquare r ≠ (⟨5, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      constructor <;>
        simp_all [applyBoard, castleBoard, boardMove, boardUpdate, Move.source,
          Move.destination, castleRookSource, castleRookDestination,
          Function.update_apply,
          hks, hkt, hrs, hrd, rks, rkt, rrs, rrd]
  | blackQueenCastle =>
      have hks : rightKingSquare r ≠ (⟨4, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hkt : rightKingSquare r ≠ (⟨2, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrs : rightKingSquare r ≠ (⟨0, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have hrd : rightKingSquare r ≠ (⟨3, by decide⟩, ⟨7, by decide⟩) :=
        hking_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rks : rightRookSquare r ≠ (⟨4, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rkt : rightRookSquare r ≠ (⟨2, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrs : rightRookSquare r ≠ (⟨0, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      have rrd : rightRookSquare r ≠ (⟨3, by decide⟩, ⟨7, by decide⟩) :=
        hrook_touched _ (by simp [Move.source, Move.destination, castleRookSource,
          castleRookDestination])
      constructor <;>
        simp_all [applyBoard, castleBoard, boardMove, boardUpdate, Move.source,
          Move.destination, castleRookSource, castleRookDestination,
          Function.update_apply,
          hks, hkt, hrs, hrd, rks, rkt, rrs, rrd]

theorem invariant_applyMove_preserves_rights_consistent (p : Position) (m : Move)
    (hrc : rightsConsistent p) : rightsConsistent (applyMove p m) := by
  intro r hr
  have hr' : r ∈ rightsAfterMove p m := by
    simpa [applyMove] using hr
  have hold : r ∈ p.castling := (Finset.mem_sdiff.mp hr').1
  have hhome := invariant_right_home_preserved p m r hr'
  have hh := hrc r hold
  constructor
  · change applyBoard p m (rightKingSquare r) =
      some ⟨rightColor r, .king⟩
    rw [hhome.1]
    exact hh.1
  · change applyBoard p m (rightRookSquare r) =
      some ⟨rightColor r, .rook⟩
    rw [hhome.2]
    exact hh.2

theorem invariant_legal_preserves_positionInvariant (p : Position) (m : Move)
    (hp : positionInvariant p) (hm : legalMove p m) :
    positionInvariant (applyMove p m) := by
  rcases hp with ⟨hkw, hkb, hpawn, hrights, hfull⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [applyMove_board] using
      invariant_pseudo_preserves_king_count p m hm.1 .white hkw
  · simpa [applyMove_board] using
      invariant_pseudo_preserves_king_count p m hm.1 .black hkb
  · simpa [applyMove_board] using
      invariant_pseudo_preserves_pawn_rank p m hm.1 hpawn
  · exact invariant_applyMove_preserves_rights_consistent p m hrights
  · cases hturn : p.turn with
    | white => simpa [applyMove, hturn] using hfull
    | black =>
        simp [applyMove, hturn]

theorem reachable_positionInvariant (p : Position) (h : reachable p) :
    positionInvariant p := by
  unfold reachable at h
  induction h with
  | refl => exact invariant_positionInvariant_initial
  | @tail q r hqr hstep ih =>
      rcases hstep with ⟨m, hm, rfl⟩
      exact invariant_legal_preserves_positionInvariant q m ih hm


end Chess
