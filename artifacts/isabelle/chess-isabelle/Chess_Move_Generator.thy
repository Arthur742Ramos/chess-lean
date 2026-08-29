section \<open>Executable move generation\<close>

theory Chess_Move_Generator
  imports Chess_Legal
begin

definition pseudo_legal_moves :: "position \<Rightarrow> move list" where
  "pseudo_legal_moves p = filter (pseudo_legal p) candidate_moves"

definition legal_moves :: "position \<Rightarrow> move list" where
  "legal_moves p = filter (legal_move p) (pseudo_legal_moves p)"

lemma pseudo_legal_moves_correct:
  "m \<in> set (pseudo_legal_moves p) \<longleftrightarrow> pseudo_legal p m"
  by (simp add: pseudo_legal_moves_def candidate_moves_complete)

lemma pseudo_legal_moves_sound:
  "m \<in> set (pseudo_legal_moves p) \<Longrightarrow> pseudo_legal p m"
  by (simp add: pseudo_legal_moves_correct)

lemma pseudo_legal_moves_complete:
  "pseudo_legal p m \<Longrightarrow> m \<in> set (pseudo_legal_moves p) "
  by (simp add: pseudo_legal_moves_correct)

lemma legal_moves_sound:
  "m \<in> set (legal_moves p) \<Longrightarrow> legal_move p m"
  by (simp add: legal_moves_def)

lemma legal_moves_complete:
  "legal_move p m \<Longrightarrow> m \<in> set (legal_moves p)"
  by (simp add: legal_moves_def pseudo_legal_moves_correct legal_move_def)

lemma legal_moves_correct:
  "m \<in> set (legal_moves p) \<longleftrightarrow> legal_move p m"
  by (simp add: legal_moves_def pseudo_legal_moves_correct legal_move_def)

lemma pseudo_legal_moves_subset_candidates:
  "set (pseudo_legal_moves p) \<subseteq> set candidate_moves"
  by (simp add: pseudo_legal_moves_def)

lemma legal_moves_subset_pseudo:
  "set (legal_moves p) \<subseteq> set (pseudo_legal_moves p)"
  by (simp add: legal_moves_def)

end
