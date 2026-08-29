section \<open>Histories and reachability\<close>

theory Chess_History
  imports Chess_Move_Generator_Correct
begin

definition legal_transition :: "(position \<times> position) set" where
  "legal_transition =
    {(p,q). \<exists>m. legal_move p m \<and> q = apply_move p m}"

definition reachable_from :: "position \<Rightarrow> position \<Rightarrow> bool" where
  "reachable_from p q \<longleftrightarrow>
    (p,q) \<in> legal_transition\<^sup>*"

definition legal_step :: "position \<Rightarrow> move \<Rightarrow> position \<Rightarrow> bool" where
  "legal_step p m q \<longleftrightarrow> legal_move p m \<and> q = apply_move p m"

fun replay :: "position \<Rightarrow> move list \<Rightarrow> position" where
  "replay p [] = p"
| "replay p (m#ms) = replay (apply_move p m) ms"

fun valid_steps :: "position list \<Rightarrow> bool" where
  "valid_steps [] = True"
| "valid_steps [p] = True"
| "valid_steps (p#q#ps) =
     ((p,q) \<in> legal_transition \<and> valid_steps (q#ps))"

definition valid_history :: "position list \<Rightarrow> bool" where
  "valid_history hs =
     (case hs of
        [] \<Rightarrow> False
      | p#ps \<Rightarrow> p = initial_position \<and> valid_steps (p#ps))"

lemma valid_history_singleton:
  "valid_history [p] \<longleftrightarrow> p = initial_position"
  by (simp add: valid_history_def)

lemma valid_history_step:
  "valid_history (p#q#ps) \<longleftrightarrow>
     p = initial_position \<and> (p,q) \<in> legal_transition \<and>
       valid_steps (q#ps)"
  by (simp add: valid_history_def)

definition reachable :: "position \<Rightarrow> bool" where
  "reachable p \<longleftrightarrow> (initial_position,p) \<in> legal_transition\<^sup>*"

definition legal_position :: "position \<Rightarrow> bool" where
  "legal_position p \<longleftrightarrow> reachable p"

lemma reachable_from_refl:
  "reachable_from p p"
  by (simp add: reachable_from_def)

lemma reachable_from_trans:
  "reachable_from p q \<Longrightarrow> reachable_from q r \<Longrightarrow>
     reachable_from p r"
  unfolding reachable_from_def
  by (rule rtrancl_trans)

lemma reachable_from_step:
  "reachable_from p q \<Longrightarrow> legal_move q m \<Longrightarrow>
     reachable_from p (apply_move q m)"
  unfolding reachable_from_def legal_transition_def
  by (auto intro: rtrancl_into_rtrancl)

lemma reachable_iff_reachable_from_initial:
  "reachable p \<longleftrightarrow> reachable_from initial_position p"
  by (simp add: reachable_def reachable_from_def)

lemma reachable_initial:
  "reachable initial_position"
  by (simp add: reachable_def)

lemma legal_step_iff:
  "legal_step p m q \<longleftrightarrow> legal_move p m \<and> q = apply_move p m"
  by (simp add: legal_step_def)

lemma legal_transitionI:
  "legal_move p m \<Longrightarrow> (p, apply_move p m) \<in> legal_transition"
  by (auto simp add: legal_transition_def)

lemma reachable_step:
  "reachable p \<Longrightarrow> legal_move p m \<Longrightarrow>
     reachable (apply_move p m)"
  unfolding reachable_def legal_transition_def
  by (auto intro: rtrancl_into_rtrancl)

lemma reachable_initial_core_invariant:
  "reachable p \<Longrightarrow>
     exactly_one_king (position_board p) White \<and>
     exactly_one_king (position_board p) Black \<and>
     \<not> pawn_on_promotion_rank (position_board p) \<and>
     position_fullmove p > 0"
unfolding reachable_def
proof (induct rule: rtrancl_induct)
  case base
  then show ?case
    by (simp add: initial_position_kings
        initial_position_no_pawn_on_promotion_rank initial_position_fullmove)
next
  case (step q r)
  obtain m where hm: "legal_move q m" and hr: "r = apply_move q m"
    using step.hyps(2) by (auto simp add: legal_transition_def)
  have hqW: "exactly_one_king (position_board q) White"
    using step.hyps(3) by blast
  have hqB: "exactly_one_king (position_board q) Black"
    using step.hyps(3) by blast
  have hqPawn:
      "\<not> pawn_on_promotion_rank (position_board q)"
    using step.hyps(3) by blast
  have hrW:
      "exactly_one_king (position_board (apply_move q m)) White"
    using pseudo_legal_preserves_king_count
      [OF legal_move_pseudo[OF hm] hqW]
    by (simp add: apply_move_board)
  have hrB:
      "exactly_one_king (position_board (apply_move q m)) Black"
    using pseudo_legal_preserves_king_count
      [OF legal_move_pseudo[OF hm] hqB]
    by (simp add: apply_move_board)
  have hrPawn:
      "\<not> pawn_on_promotion_rank (position_board (apply_move q m))"
    using pseudo_legal_preserves_pawn_rank
      [OF legal_move_pseudo[OF hm] hqPawn]
    by (simp add: apply_move_board)
  have hqfm: "position_fullmove q > 0"
    using step.hyps(3) by blast
  have hfm: "position_fullmove (apply_move q m) > 0"
    using hqfm by (simp add: fullmove_clock_apply_move)
  show ?case using hr hrW hrB hrPawn hfm by simp
qed

lemma reachable_position_invariant:
  "reachable p \<Longrightarrow> position_invariant p"
unfolding reachable_def
proof (induct rule: rtrancl_induct)
  case base
  show ?case
    by (simp add: position_invariant_def initial_position_kings
        initial_position_no_pawn_on_promotion_rank initial_position_rights_consistent
        initial_position_fullmove)
next
  case (step q r)
  obtain m where hm: "legal_move q m" and hr: "r = apply_move q m"
    using step.hyps(2) by (auto simp add: legal_transition_def)
  have hq: "position_invariant q"
    using step.hyps(3) .
  show ?case
    using legal_move_preserves_position_invariant[OF hq hm] hr by simp
qed

lemma replay_append:
  "replay p (xs @ ys) = replay (replay p xs) ys"
  by (induct xs arbitrary: p) simp_all

end
