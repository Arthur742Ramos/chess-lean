section \<open>Bounded forced mate\<close>

theory Chess_Mate
  imports Chess_Game Chess_Move_Generator_Correct
begin

text \<open>
  The original position-only predicate below is retained as a small
  compatibility theorem for existing certificates.  The public search
  interface is the history-aware bounded-mate predicate:
  its list is in game order and the
  current position is the last element.  This matters for repetition, whose
  key is a property of the whole game history rather than of a position in
  isolation.
\<close>

fun forced_mate_within :: "color \<Rightarrow> position \<Rightarrow> nat \<Rightarrow> bool" where
  "forced_mate_within c p 0 =
     (checkmate p \<and> position_turn p = opponent c)"
| "forced_mate_within c p (Suc n) =
     (if checkmate p then position_turn p = opponent c
      else if stalemate p \<or> dead_position p \<or>
              fivefold_repetition [p] \<or> seventy_five_move_draw p
      then False
      else if position_turn p = c
      then list_ex (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p)
      else list_all (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p))"

definition mate_in_position :: "color \<Rightarrow> position \<Rightarrow> nat \<Rightarrow> bool" where
  "mate_in_position c p n \<longleftrightarrow> forced_mate_within c p n"

lemma forced_mate_within_def:
  "forced_mate_within c p 0 =
     (checkmate p \<and> position_turn p = opponent c) \<and>
   forced_mate_within c p (Suc n) =
     (if checkmate p then position_turn p = opponent c
      else if stalemate p \<or> dead_position p \<or>
              fivefold_repetition [p] \<or> seventy_five_move_draw p
      then False
      else if position_turn p = c
      then list_ex (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p)
      else list_all (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p))"
  by simp_all

lemma mate_in_position_correct:
  "mate_in_position c p n \<longleftrightarrow> forced_mate_within c p n"
  by (simp add: mate_in_position_def)

lemma mate_in_correct:
  "mate_in_position c p n \<longleftrightarrow> forced_mate_within c p n"
  by (rule mate_in_position_correct)

lemma forced_mate_zero:
  "forced_mate_within c p 0 \<longleftrightarrow>
     checkmate p \<and> position_turn p = opponent c"
  by simp

text \<open>
  A terminal predicate is made an explicit parameter of the executable
  search.  The semantic specialization includes Isabelle's exact
  reflexive-transitive dead-position definition; the executable
  specialization deliberately leaves that predicate to its caller.  Thus
  code generation never silently treats an unbounded reachability predicate
  as a decision procedure.
\<close>

definition history_current :: "position list \<Rightarrow> position option" where
  "history_current hs = (case rev hs of [] \<Rightarrow> None | p#ps \<Rightarrow> Some p)"

definition semantic_mate_terminal :: "position list \<Rightarrow> bool" where
  "semantic_mate_terminal hs =
    (case history_current hs of
       None \<Rightarrow> True
     | Some p \<Rightarrow>
         dead_position p \<or> fivefold_repetition hs \<or>
         seventy_five_move_draw p)"

definition executable_mate_terminal :: "position list \<Rightarrow> bool" where
  "executable_mate_terminal hs =
    (case history_current hs of
       None \<Rightarrow> True
     | Some p \<Rightarrow>
         fivefold_repetition hs \<or> seventy_five_move_draw p)"

definition semantic_mate_claim_current :: "position list \<Rightarrow> bool" where
  "semantic_mate_claim_current hs =
    (case history_current hs of
       None \<Rightarrow> False
     | Some p \<Rightarrow> threefold_claimable hs \<or> fifty_move_claimable p)"

definition semantic_mate_claim_after ::
    "position list \<Rightarrow> move \<Rightarrow> bool" where
  "semantic_mate_claim_after hs m =
    (case history_current hs of
       None \<Rightarrow> False
     | Some p \<Rightarrow>
         threefold_claimable_after hs m \<or>
         fifty_move_claimable_after p m)"

definition executable_mate_claim_current :: "position list \<Rightarrow> bool" where
  "executable_mate_claim_current hs = semantic_mate_claim_current hs"

definition executable_mate_claim_after ::
    "position list \<Rightarrow> move \<Rightarrow> bool" where
  "executable_mate_claim_after hs m = semantic_mate_claim_after hs m"

text \<open>
  The policy parameter below separates automatic terminal draws from optional
  claims.  Claims are only checked at defender nodes: the attacker may decline
  to claim, while a defender may stop the line either at a currently claimable
  position or by announcing a legal intended move that makes a claimable
  position.
\<close>

fun forced_mate_within_policy ::
    "color \<Rightarrow> (position list \<Rightarrow> bool) \<Rightarrow>
     (position list \<Rightarrow> bool) \<Rightarrow>
     (position list \<Rightarrow> move \<Rightarrow> bool) \<Rightarrow>
     position list \<Rightarrow> nat \<Rightarrow> bool" where
  "forced_mate_within_policy c terminal claim_current claim_after hs 0 =
     (case history_current hs of
        None \<Rightarrow> False
      | Some p \<Rightarrow> checkmate p \<and> position_turn p = opponent c)"
| "forced_mate_within_policy c terminal claim_current claim_after hs (Suc n) =
     (case history_current hs of
        None \<Rightarrow> False
      | Some p \<Rightarrow>
          if checkmate p then position_turn p = opponent c
          else if stalemate p \<or> terminal hs
          then False
          else if position_turn p = c
          then list_ex
            (\<lambda>m. forced_mate_within_policy c terminal
               claim_current claim_after
               (hs @ [apply_move p m]) n) (legal_moves p)
          else if claim_current hs then False
          else list_all
            (\<lambda>m. \<not> claim_after hs m \<and>
              forced_mate_within_policy c terminal claim_current claim_after
               (hs @ [apply_move p m]) n) (legal_moves p))"

definition forced_mate_within_terminal ::
    "color \<Rightarrow> (position list \<Rightarrow> bool) \<Rightarrow>
     position list \<Rightarrow> nat \<Rightarrow> bool" where
  "forced_mate_within_terminal c terminal hs n =
     forced_mate_within_policy c terminal
       (\<lambda>_. False) (\<lambda>_ _. False) hs n"

definition forced_mate_within_history ::
    "color \<Rightarrow> position list \<Rightarrow> nat \<Rightarrow> bool" where
  "forced_mate_within_history c hs n =
     forced_mate_within_policy c semantic_mate_terminal
       semantic_mate_claim_current semantic_mate_claim_after hs n"

definition forced_mate_within_executable ::
    "color \<Rightarrow> position list \<Rightarrow> nat \<Rightarrow> bool" where
  "forced_mate_within_executable c hs n =
     forced_mate_within_policy c executable_mate_terminal
       executable_mate_claim_current executable_mate_claim_after hs n"

definition mate_in ::
    "color \<Rightarrow> position list \<Rightarrow> nat \<Rightarrow> bool" where
  "mate_in c hs n \<longleftrightarrow> forced_mate_within_history c hs n"

lemma forced_mate_within_policy_recurrence:
  "forced_mate_within_policy c terminal claim_current claim_after hs 0 =
      (case history_current hs of
         None \<Rightarrow> False
       | Some p \<Rightarrow> checkmate p \<and> position_turn p = opponent c) \<and>
   forced_mate_within_policy c terminal claim_current claim_after hs (Suc n) =
      (case history_current hs of
         None \<Rightarrow> False
       | Some p \<Rightarrow>
           if checkmate p then position_turn p = opponent c
           else if stalemate p \<or> terminal hs
           then False
           else if position_turn p = c
           then list_ex
             (\<lambda>m. forced_mate_within_policy c terminal
               claim_current claim_after
               (hs @ [apply_move p m]) n) (legal_moves p)
           else if claim_current hs then False
           else list_all
             (\<lambda>m. \<not> claim_after hs m \<and>
               forced_mate_within_policy c terminal claim_current claim_after
               (hs @ [apply_move p m]) n) (legal_moves p))"
  by simp

lemma forced_mate_within_history_recurrence:
  "forced_mate_within_history c hs 0 =
      (case history_current hs of
         None \<Rightarrow> False
       | Some p \<Rightarrow> checkmate p \<and> position_turn p = opponent c) \<and>
   forced_mate_within_history c hs (Suc n) =
      (case history_current hs of
         None \<Rightarrow> False
       | Some p \<Rightarrow>
           if checkmate p then position_turn p = opponent c
           else if stalemate p \<or> semantic_mate_terminal hs
           then False
           else if position_turn p = c
           then list_ex
             (\<lambda>m. forced_mate_within_history c
               (hs @ [apply_move p m]) n) (legal_moves p)
           else if semantic_mate_claim_current hs then False
           else list_all
             (\<lambda>m. \<not> semantic_mate_claim_after hs m \<and>
               forced_mate_within_history c
               (hs @ [apply_move p m]) n) (legal_moves p))"
  unfolding forced_mate_within_history_def
  by (simp add: forced_mate_within_policy.simps)

lemma forced_mate_within_history_refinement:
  "forced_mate_within_history c hs n =
   forced_mate_within_policy c semantic_mate_terminal
     semantic_mate_claim_current semantic_mate_claim_after hs n"
  by (simp add: forced_mate_within_history_def)

lemma forced_mate_within_policy_current_claim:
  assumes "history_current hs = Some p"
    and "\<not> checkmate p"
    and "\<not> stalemate p"
    and "\<not> terminal hs"
    and "position_turn p \<noteq> c"
    and "claim_current hs"
  shows "\<not> forced_mate_within_policy c terminal claim_current
    claim_after hs (Suc n)"
  using assms
  by (simp add: forced_mate_within_policy.simps)

lemma forced_mate_within_policy_announced_claim:
  assumes "history_current hs = Some p"
    and "\<not> checkmate p"
    and "\<not> stalemate p"
    and "\<not> terminal hs"
    and "position_turn p \<noteq> c"
    and "\<not> claim_current hs"
    and "m \<in> set (legal_moves p)"
    and "claim_after hs m"
  shows "\<not> forced_mate_within_policy c terminal claim_current
    claim_after hs (Suc n)"
proof -
  have hnotall:
      "\<not> list_all
        (\<lambda>m. \<not> claim_after hs m \<and>
          forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n) (legal_moves p)"
  proof
    assume hall:
        "list_all
          (\<lambda>m. \<not> claim_after hs m \<and>
            forced_mate_within_policy c terminal claim_current claim_after
              (hs @ [apply_move p m]) n) (legal_moves p)"
    have hall':
        "\<forall>x \<in> set (legal_moves p).
          \<not> claim_after hs x \<and>
          forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p x]) n"
      using hall by (simp add: list_all_iff)
    have hitem:
        "\<not> claim_after hs m \<and>
          forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n"
      using hall' assms by blast
    show False using hitem assms by blast
  qed
  show ?thesis
    using assms hnotall
    by (simp add: forced_mate_within_policy.simps)
qed

lemma mate_in_history_correct:
  "mate_in c hs n \<longleftrightarrow> forced_mate_within_history c hs n"
  by (simp add: mate_in_def)

lemma forced_mate_within_history_singleton_zero:
  "forced_mate_within_history c [p] 0 \<longleftrightarrow>
     checkmate p \<and> position_turn p = opponent c"
  by (simp add: forced_mate_within_history_def
      forced_mate_within_policy.simps history_current_def)

end
