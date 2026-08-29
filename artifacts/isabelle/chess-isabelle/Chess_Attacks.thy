section \<open>Geometric attacks\<close>

theory Chess_Attacks
  imports Chess_Geometry
begin

definition slider_attack :: "position \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "slider_attack p s t \<longleftrightarrow> clear_between (position_board p) s t"

definition piece_attacks :: "position \<Rightarrow> color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "piece_attacks p c s t \<longleftrightarrow>
    (case position_board p s of
       Some q \<Rightarrow>
         piece_color q = c \<and>
         ((piece_kind q = Rook \<and> rook_geometry s t \<and> slider_attack p s t) \<or>
          (piece_kind q = Bishop \<and> bishop_geometry s t \<and> slider_attack p s t) \<or>
          (piece_kind q = Queen \<and> queen_geometry s t \<and> slider_attack p s t) \<or>
          (piece_kind q = Knight \<and> knight_geometry s t) \<or>
          (piece_kind q = King \<and> king_geometry s t) \<or>
          (piece_kind q = Pawn \<and> pawn_attack_geometry c s t))
     | None \<Rightarrow> False)"

definition is_attacked :: "position \<Rightarrow> color \<Rightarrow> square \<Rightarrow> bool" where
  "is_attacked p c t \<longleftrightarrow>
    list_ex (\<lambda>s. piece_attacks p c s t) all_squares"

definition attacked_squares :: "position \<Rightarrow> color \<Rightarrow> square list" where
  "attacked_squares p c = filter (\<lambda>t. is_attacked p c t) all_squares"

lemma piece_attacks_empty_source:
  "position_board p s = None \<Longrightarrow> \<not> piece_attacks p c s t"
  by (simp add: piece_attacks_def)

lemma is_attacked_iff:
  "is_attacked p c t \<longleftrightarrow> (\<exists>s. piece_attacks p c s t)"
  by (simp add: is_attacked_def list_ex_iff all_squares_set)

lemma attacked_squares_correct:
  "t \<in> set (attacked_squares p c) \<longleftrightarrow> is_attacked p c t"
  by (simp add: attacked_squares_def all_squares_set)

end
