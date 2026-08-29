section \<open>Check and king lookup\<close>

theory Chess_Check
  imports Chess_Attacks
begin

definition king_square :: "board \<Rightarrow> color \<Rightarrow> square option" where
  "king_square b c = List.find (\<lambda>s. has_piece b s c King) all_squares"

definition in_check :: "position \<Rightarrow> color \<Rightarrow> bool" where
  "in_check p c \<longleftrightarrow>
    (case king_square (position_board p) c of
       Some s \<Rightarrow> is_attacked p (opponent c) s
     | None \<Rightarrow> True)"

lemma king_square_none_iff:
  "king_square b c = None \<longleftrightarrow>
     (\<forall>s \<in> set all_squares. \<not> has_piece b s c King)"
  by (auto simp add: king_square_def find_None_iff)

lemma king_square_some:
  "king_square b c = Some s \<Longrightarrow>
     s \<in> set all_squares \<and> has_piece b s c King"
  by (auto simp add: king_square_def find_Some_iff all_squares_set)

lemma in_check_iff:
  "king_square (position_board p) c = Some s \<Longrightarrow>
     in_check p c \<longleftrightarrow> is_attacked p (opponent c) s"
  by (simp add: in_check_def)

end
