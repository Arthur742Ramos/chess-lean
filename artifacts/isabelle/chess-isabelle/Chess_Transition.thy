section \<open>Deterministic chess transitions\<close>

theory Chess_Transition
  imports Chess_En_Passant Chess_Promotion Chess_Castling
begin

definition moving_piece :: "position \<Rightarrow> move \<Rightarrow> piece option" where
  "moving_piece p m = position_board p (move_source m)"

definition moving_color :: "position \<Rightarrow> move \<Rightarrow> color" where
  "moving_color p m =
    (case moving_piece p m of Some q \<Rightarrow> piece_color q | None \<Rightarrow> position_turn p)"

definition move_capture_square :: "position \<Rightarrow> move \<Rightarrow> square option" where
  "move_capture_square p m =
    (case m of
       Normal s t \<Rightarrow> if position_board p t = None then None else Some t
     | Promotion s t k \<Rightarrow> if position_board p t = None then None else Some t
     | EnPassant s t \<Rightarrow> ep_captured_square (position_turn p) t
     | _ \<Rightarrow> None)"

definition move_is_capture :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "move_is_capture p m \<longleftrightarrow>
    (case move_capture_square p m of
       Some s \<Rightarrow> position_board p s \<noteq> None
     | None \<Rightarrow> False)"

definition move_is_pawn :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "move_is_pawn p m \<longleftrightarrow>
    (case m of
       Promotion s t k \<Rightarrow> True
     | EnPassant s t \<Rightarrow> True
     | _ \<Rightarrow>
         (case moving_piece p m of
            Some q \<Rightarrow> piece_kind q = Pawn
          | None \<Rightarrow> False))"

definition rights_removed_for_square :: "square \<Rightarrow> castling_rights" where
  "rights_removed_for_square s =
    (if s = (E,R1) then {WhiteKingSide, WhiteQueenSide}
     else if s = (A,R1) then {WhiteQueenSide}
     else if s = (H,R1) then {WhiteKingSide}
     else if s = (E,R8) then {BlackKingSide, BlackQueenSide}
     else if s = (A,R8) then {BlackQueenSide}
     else if s = (H,R8) then {BlackKingSide}
     else {})"

definition moving_rights_removed :: "position \<Rightarrow> move \<Rightarrow> castling_rights" where
  "moving_rights_removed p m =
    (case moving_piece p m of
       Some q \<Rightarrow>
         if piece_kind q = King \<or> piece_kind q = Rook
         then rights_removed_for_square (move_source m) else {}
     | None \<Rightarrow> {})"

definition captured_rights_removed :: "position \<Rightarrow> move \<Rightarrow> castling_rights" where
  "captured_rights_removed p m =
    (case move_capture_square p m of
       Some s \<Rightarrow>
         (case position_board p s of
            Some q \<Rightarrow> if piece_kind q = Rook
              then rights_removed_for_square s else {}
          | None \<Rightarrow> {})
     | None \<Rightarrow> {})"

definition rights_removed_for_move :: "position \<Rightarrow> move \<Rightarrow> castling_rights" where
  "rights_removed_for_move p m =
    (case m of
       Normal s t \<Rightarrow>
         rights_removed_for_square s \<union> rights_removed_for_square t
     | Promotion s t k \<Rightarrow>
         rights_removed_for_square s \<union> rights_removed_for_square t
     | EnPassant s t \<Rightarrow>
         rights_removed_for_square s \<union> rights_removed_for_square t \<union>
           (case ep_captured_square (position_turn p) t of
              Some cs \<Rightarrow> rights_removed_for_square cs | None \<Rightarrow> {})
     | WhiteKingCastle \<Rightarrow>
         rights_removed_for_square (E,R1) \<union>
           rights_removed_for_square (H,R1) \<union>
           rights_removed_for_square (G,R1) \<union>
           rights_removed_for_square (F,R1)
     | WhiteQueenCastle \<Rightarrow>
         rights_removed_for_square (E,R1) \<union>
           rights_removed_for_square (A,R1) \<union>
           rights_removed_for_square (C,R1) \<union>
           rights_removed_for_square (D,R1)
     | BlackKingCastle \<Rightarrow>
         rights_removed_for_square (E,R8) \<union>
           rights_removed_for_square (H,R8) \<union>
           rights_removed_for_square (G,R8) \<union>
           rights_removed_for_square (F,R8)
     | BlackQueenCastle \<Rightarrow>
         rights_removed_for_square (E,R8) \<union>
           rights_removed_for_square (A,R8) \<union>
           rights_removed_for_square (C,R8) \<union>
           rights_removed_for_square (D,R8))"

definition rights_after_move :: "position \<Rightarrow> move \<Rightarrow> castling_rights" where
  "rights_after_move p m =
    position_castling p - rights_removed_for_move p m"

lemma rights_after_move_member_old:
  "r \<in> rights_after_move p m \<Longrightarrow> r \<in> position_castling p"
  by (simp add: rights_after_move_def)

definition pawn_double_target ::
    "color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> square option" where
  "pawn_double_target c s t =
    (if pawn_double_geometry c s t then
       Some (fst s, if c = White then R3 else R6)
     else None)"

definition new_en_passant :: "position \<Rightarrow> move \<Rightarrow> square option" where
  "new_en_passant p m =
    (case m of
       Normal s t \<Rightarrow>
         (case position_board p s of
            Some q \<Rightarrow>
              if piece_kind q = Pawn
              then pawn_double_target (piece_color q) s t else None
          | None \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition castle_board :: "position \<Rightarrow> move \<Rightarrow> board" where
  "castle_board p m =
    (case (castle_rook_source m, castle_rook_destination m) of
       (Some rs, Some rd) \<Rightarrow>
         board_update
           (board_update
             (board_move (position_board p) (move_source m) (move_destination m))
             rs None)
           rd (position_board p rs)
     | _ \<Rightarrow> position_board p)"

definition apply_board :: "position \<Rightarrow> move \<Rightarrow> board" where
  "apply_board p m =
    (case m of
       Normal s t \<Rightarrow> board_move (position_board p) s t
     | Promotion s t k \<Rightarrow>
         board_update
           (board_update (position_board p) s None)
           t (Some \<lparr>piece_color = moving_color p m,
                piece_kind = promotion_piece_kind k\<rparr>)
     | EnPassant s t \<Rightarrow>
         (case ep_captured_square (position_turn p) t of
            Some cs \<Rightarrow>
              board_update
                (board_move (position_board p) s t) cs None
          | None \<Rightarrow> board_move (position_board p) s t)
     | WhiteKingCastle \<Rightarrow> castle_board p m
     | WhiteQueenCastle \<Rightarrow> castle_board p m
     | BlackKingCastle \<Rightarrow> castle_board p m
     | BlackQueenCastle \<Rightarrow> castle_board p m)"

definition apply_move :: "position \<Rightarrow> move \<Rightarrow> position" where
  "apply_move p m =
    \<lparr>position_board = apply_board p m,
     position_turn = opponent (position_turn p),
     position_castling = rights_after_move p m,
     position_en_passant = new_en_passant p m,
     position_halfmove =
       (if move_is_pawn p m \<or> move_is_capture p m
        then 0 else position_halfmove p + 1),
     position_fullmove =
       (if position_turn p = Black
        then position_fullmove p + 1 else position_fullmove p)\<rparr>"

lemma turn_apply_move:
  "position_turn (apply_move p m) = opponent (position_turn p)"
  by (simp add: apply_move_def)

lemma halfmove_clock_apply_move:
  "position_halfmove (apply_move p m) =
    (if move_is_pawn p m \<or> move_is_capture p m
     then 0 else position_halfmove p + 1)"
  by (simp add: apply_move_def)

lemma fullmove_clock_apply_move:
  "position_fullmove (apply_move p m) =
    (if position_turn p = Black
     then position_fullmove p + 1 else position_fullmove p)"
  by (simp add: apply_move_def)

lemma apply_move_board:
  "position_board (apply_move p m) = apply_board p m"
  by (simp add: apply_move_def)

lemma apply_move_simps:
  "position_board (apply_move p m) = apply_board p m \<and>
   position_turn (apply_move p m) = opponent (position_turn p) \<and>
   position_castling (apply_move p m) = rights_after_move p m \<and>
   position_en_passant (apply_move p m) = new_en_passant p m \<and>
   position_halfmove (apply_move p m) =
     (if move_is_pawn p m \<or> move_is_capture p m
      then 0 else position_halfmove p + 1) \<and>
   position_fullmove (apply_move p m) =
     (if position_turn p = Black
      then position_fullmove p + 1 else position_fullmove p)"
  by (simp add: apply_move_def)

lemma apply_en_passant_board:
  "apply_board p (EnPassant s t) =
    (case ep_captured_square (position_turn p) t of
       Some cs \<Rightarrow>
         board_update (board_move (position_board p) s t) cs None
     | None \<Rightarrow> board_move (position_board p) s t)"
  by (simp add: apply_board_def)

lemma apply_promotion_destination:
  "apply_board p (Promotion s t k) t =
    Some \<lparr>piece_color = moving_color p (Promotion s t k),
      piece_kind = promotion_piece_kind k\<rparr>"
  by (simp add: apply_board_def board_update_def)

end
