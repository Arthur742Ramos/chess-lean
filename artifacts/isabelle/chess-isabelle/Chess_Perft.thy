section \<open>Perft\<close>

theory Chess_Perft
  imports Chess_Move_Generator_Correct Chess_Transition
begin

fun perft :: "position \<Rightarrow> nat \<Rightarrow> nat" where
  "perft p 0 = 1"
| "perft p (Suc n) =
    sum_list (map (\<lambda>m. perft (apply_move p m) n) (legal_moves p))"

definition perft_divide :: "position \<Rightarrow> nat \<Rightarrow> (move \<times> nat) list" where
  "perft_divide p n =
    map (\<lambda>m. (m, perft (apply_move p m) n)) (legal_moves p)"

lemma perft_zero: "perft p 0 = 1"
  by simp

lemma perft_Suc:
  "perft p (Suc n) =
    sum_list (map (\<lambda>m. perft (apply_move p m) n) (legal_moves p))"
  by simp

lemma perft_divide_fst:
  "map fst (perft_divide p n) = legal_moves p"
  by (simp add: perft_divide_def comp_def)

end
