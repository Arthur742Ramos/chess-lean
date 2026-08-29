section \<open>Chess boards\<close>

theory Chess_Board
  imports Chess_Square
begin

type_synonym board = "square \<Rightarrow> piece option"

definition empty_board :: board where
  "empty_board = (\<lambda>_. None)"

definition piece_at :: "board \<Rightarrow> square \<Rightarrow> piece option" where
  "piece_at b s = b s"

definition occupied :: "board \<Rightarrow> square \<Rightarrow> bool" where
  "occupied b s \<longleftrightarrow> b s \<noteq> None"

definition occupied_by :: "board \<Rightarrow> color \<Rightarrow> square \<Rightarrow> bool" where
  "occupied_by b c s \<longleftrightarrow> (\<exists>p. b s = Some p \<and> piece_color p = c)"

definition squares_of :: "board \<Rightarrow> color \<Rightarrow> piece_kind \<Rightarrow> square set" where
  "squares_of b c k = {s. \<exists>p. b s = Some p \<and> piece_color p = c \<and> piece_kind p = k}"

definition pieces_of :: "board \<Rightarrow> color \<Rightarrow> piece_kind \<Rightarrow> piece set" where
  "pieces_of b c k = {p. \<exists>s. b s = Some p \<and>
      piece_color p = c \<and> piece_kind p = k}"

definition board_update :: "board \<Rightarrow> square \<Rightarrow> piece option \<Rightarrow> board" where
  "board_update b s p = b(s := p)"

definition board_move :: "board \<Rightarrow> square \<Rightarrow> square \<Rightarrow> board" where
  "board_move b s t = board_update (board_update b s None) t (b s)"

definition board_capture :: "board \<Rightarrow> square \<Rightarrow> square \<Rightarrow> board" where
  "board_capture b s t = board_move b s t"

lemma empty_board_simps: "empty_board s = None" "\<not> occupied empty_board s"
  by (simp_all add: empty_board_def occupied_def)

lemma occupied_iff: "occupied b s \<longleftrightarrow> (\<exists>p. b s = Some p)"
  by (simp add: occupied_def split: option.splits)

lemma occupied_by_iff:
  "occupied_by b c s \<longleftrightarrow> (\<exists>p. b s = Some p \<and> piece_color p = c)"
  by (simp add: occupied_by_def)

lemma board_update_same: "board_update b s p s = p"
  by (simp add: board_update_def)

lemma board_update_other:
  "t \<noteq> s \<Longrightarrow> board_update b s p t = b t"
  by (simp add: board_update_def)

lemma board_ext: "(\<And>s. b s = c s) \<Longrightarrow> b = c"
  by (rule ext)

lemma squares_of_subset: "squares_of b c k \<subseteq> UNIV"
  by blast

lemma board_move_source: "s \<noteq> t \<Longrightarrow> board_move b s t s = None"
  by (simp add: board_move_def board_update_def)

lemma board_move_destination: "board_move b s t t = b s"
  by (simp add: board_move_def board_update_def)

end
