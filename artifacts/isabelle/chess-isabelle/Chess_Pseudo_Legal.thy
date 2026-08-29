section \<open>Pseudo-legal chess moves\<close>

theory Chess_Pseudo_Legal
  imports Chess_Castling Chess_En_Passant Chess_Promotion Chess_Transition
begin

definition destination_friendly :: "position \<Rightarrow> color \<Rightarrow> square \<Rightarrow> bool" where
  "destination_friendly p c t \<longleftrightarrow>
    (case position_board p t of
       None \<Rightarrow> True
     | Some q \<Rightarrow> piece_color q \<noteq> c \<and> piece_kind q \<noteq> King)"

definition normal_piece_geometry ::
    "position \<Rightarrow> color \<Rightarrow> piece \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "normal_piece_geometry p c q s t \<longleftrightarrow>
    (case piece_kind q of
       Rook \<Rightarrow> rook_geometry s t \<and>
         clear_between (position_board p) s t
     | Bishop \<Rightarrow> bishop_geometry s t \<and>
         clear_between (position_board p) s t
     | Queen \<Rightarrow> queen_geometry s t \<and>
         clear_between (position_board p) s t
     | Knight \<Rightarrow> knight_geometry s t
     | King \<Rightarrow> king_geometry s t
     | Pawn \<Rightarrow>
         ((pawn_move_geometry c s t \<and> position_board p t = None) \<or>
          (pawn_attack_geometry c s t \<and>
            (case position_board p t of
               Some q' \<Rightarrow> piece_color q' = opponent c
             | None \<Rightarrow> False)) \<or>
          (pawn_double_geometry c s t \<and>
            position_board p t = None \<and>
            clear_between (position_board p) s t)))"

definition normal_pseudo_legal :: "position \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "normal_pseudo_legal p s t \<longleftrightarrow>
    (case position_board p s of
       Some q \<Rightarrow>
         piece_color q = position_turn p \<and>
         destination_friendly p (position_turn p) t \<and>
         (piece_kind q \<noteq> Pawn \<or>
           snd t \<noteq> promotion_rank (position_turn p)) \<and>
         normal_piece_geometry p (position_turn p) q s t
     | None \<Rightarrow> False)"

definition pseudo_legal :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "pseudo_legal p m \<longleftrightarrow>
    (case m of
       Normal s t \<Rightarrow> normal_pseudo_legal p s t
     | Promotion s t k \<Rightarrow> pseudo_legal_promotion p m
     | EnPassant s t \<Rightarrow> pseudo_legal_en_passant p m
     | WhiteKingCastle \<Rightarrow> pseudo_legal_castle p m
     | WhiteQueenCastle \<Rightarrow> pseudo_legal_castle p m
     | BlackKingCastle \<Rightarrow> pseudo_legal_castle p m
     | BlackQueenCastle \<Rightarrow> pseudo_legal_castle p m)"

lemma normal_pseudo_legal_turn:
  "normal_pseudo_legal p s t \<Longrightarrow>
     position_board p s \<noteq> None"
  by (cases "position_board p s"; simp add: normal_pseudo_legal_def)

lemma pseudo_legal_source:
  "pseudo_legal p m \<Longrightarrow>
     position_board p (move_source m) \<noteq> None"
  by (cases m;
      auto simp add: pseudo_legal_def normal_pseudo_legal_def has_piece_def
        pseudo_legal_promotion_def pseudo_legal_en_passant_def
        pseudo_legal_castle_def move_source.simps split: option.splits)

lemma normal_pseudo_legal_source_destination:
  "normal_pseudo_legal p s t \<Longrightarrow> s \<noteq> t"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def
      rook_geometry_def bishop_geometry_def queen_geometry_def knight_geometry_def
      king_geometry_def pawn_move_geometry_def pawn_double_geometry_def
      pawn_attack_geometry_def split: option.splits)

lemma normal_pseudo_legal_destination_no_king:
  "normal_pseudo_legal p s t \<Longrightarrow>
   \<not> has_piece (position_board p) t c King"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      has_piece_def split: option.splits)

end
