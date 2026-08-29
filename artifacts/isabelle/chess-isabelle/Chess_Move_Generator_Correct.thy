section \<open>Move-generator correctness\<close>

theory Chess_Move_Generator_Correct
  imports Chess_Move_Generator
begin

lemma legal_moves_sound:
  "m \<in> set (legal_moves p) \<Longrightarrow> legal_move p m"
  by (rule Chess_Move_Generator.legal_moves_sound)

lemma legal_moves_complete:
  "legal_move p m \<Longrightarrow> m \<in> set (legal_moves p)"
  by (rule Chess_Move_Generator.legal_moves_complete)

lemma legal_moves_correct:
  "m \<in> set (legal_moves p) \<longleftrightarrow> legal_move p m"
  by (rule Chess_Move_Generator.legal_moves_correct)

lemma pseudo_legal_moves_correct:
  "m \<in> set (pseudo_legal_moves p) \<longleftrightarrow> pseudo_legal p m"
  by (rule Chess_Move_Generator.pseudo_legal_moves_correct)

end
