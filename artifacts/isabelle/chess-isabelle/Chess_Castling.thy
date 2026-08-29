section \<open>Castling prerequisites\<close>

theory Chess_Castling
  imports Chess_Attacks Chess_Move
begin

fun castle_right_of :: "move \<Rightarrow> castle_right option" where
  "castle_right_of WhiteKingCastle = Some WhiteKingSide"
| "castle_right_of WhiteQueenCastle = Some WhiteQueenSide"
| "castle_right_of BlackKingCastle = Some BlackKingSide"
| "castle_right_of BlackQueenCastle = Some BlackQueenSide"
| "castle_right_of _ = None"

fun castle_color_of :: "move \<Rightarrow> color option" where
  "castle_color_of WhiteKingCastle = Some White"
| "castle_color_of WhiteQueenCastle = Some White"
| "castle_color_of BlackKingCastle = Some Black"
| "castle_color_of BlackQueenCastle = Some Black"
| "castle_color_of _ = None"

fun castle_rook_source :: "move \<Rightarrow> square option" where
  "castle_rook_source WhiteKingCastle = Some (H, R1)"
| "castle_rook_source WhiteQueenCastle = Some (A, R1)"
| "castle_rook_source BlackKingCastle = Some (H, R8)"
| "castle_rook_source BlackQueenCastle = Some (A, R8)"
| "castle_rook_source _ = None"

fun castle_rook_destination :: "move \<Rightarrow> square option" where
  "castle_rook_destination WhiteKingCastle = Some (F, R1)"
| "castle_rook_destination WhiteQueenCastle = Some (D, R1)"
| "castle_rook_destination BlackKingCastle = Some (F, R8)"
| "castle_rook_destination BlackQueenCastle = Some (D, R8)"
| "castle_rook_destination _ = None"

fun castle_transit_square :: "move \<Rightarrow> square option" where
  "castle_transit_square WhiteKingCastle = Some (F, R1)"
| "castle_transit_square WhiteQueenCastle = Some (D, R1)"
| "castle_transit_square BlackKingCastle = Some (F, R8)"
| "castle_transit_square BlackQueenCastle = Some (D, R8)"
| "castle_transit_square _ = None"

definition castle_empty_squares :: "move \<Rightarrow> square list" where
  "castle_empty_squares m =
    (case m of
       WhiteKingCastle \<Rightarrow> [(F,R1), (G,R1)]
     | WhiteQueenCastle \<Rightarrow> [(B,R1), (C,R1), (D,R1)]
     | BlackKingCastle \<Rightarrow> [(F,R8), (G,R8)]
     | BlackQueenCastle \<Rightarrow> [(B,R8), (C,R8), (D,R8)]
     | _ \<Rightarrow> [])"

definition castle_clear :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "castle_clear p m \<longleftrightarrow>
    (\<forall>s \<in> set (castle_empty_squares m). position_board p s = None)"

definition pseudo_legal_castle :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "pseudo_legal_castle p m \<longleftrightarrow>
    (case (castle_color_of m, castle_right_of m, castle_rook_source m) of
       (Some c, Some r, Some rs) \<Rightarrow>
         position_turn p = c \<and>
         r \<in> position_castling p \<and>
         has_piece (position_board p) (E, if c = White then R1 else R8) c King \<and>
         has_piece (position_board p) rs c Rook \<and>
         castle_clear p m
     | _ \<Rightarrow> False)"

definition castle_safe_squares :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "castle_safe_squares p m \<longleftrightarrow>
    (case (castle_color_of m, castle_transit_square m) of
       (Some c, Some u) \<Rightarrow>
         \<not> is_attacked p (opponent c) (move_source m) \<and>
         \<not> is_attacked p (opponent c) u \<and>
         \<not> is_attacked p (opponent c) (move_destination m)
     | _ \<Rightarrow> False)"

lemma castle_clear_iff:
  "castle_clear p m \<longleftrightarrow>
    (\<forall>s \<in> set (castle_empty_squares m). position_board p s = None)"
  by (simp add: castle_clear_def)

end
