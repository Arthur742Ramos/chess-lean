section \<open>Draw rules\<close>

theory Chess_Draws
  imports Chess_Repetition Chess_Check Chess_Move_Generator_Correct
begin

datatype draw_reason =
    RepetitionDraw
  | FiftyMoveDraw
  | SeventyFiveMoveDraw
  | DeadPositionDraw
  | StalemateDraw

definition current_mate :: "position \<Rightarrow> bool" where
  "current_mate p \<longleftrightarrow>
    in_check p (position_turn p) \<and> legal_moves p = []"

definition dead_position :: "position \<Rightarrow> bool" where
  "dead_position p \<longleftrightarrow>
    \<not> (\<exists>q. (p,q) \<in> legal_transition\<^sup>* \<and> current_mate q)"

lemma legal_move_child_current_mate_not_dead:
  assumes "legal_move p m"
    and "current_mate (apply_move p m)"
  shows "\<not> dead_position p"
proof
  assume "dead_position p"
  have hstep: "(p, apply_move p m) \<in> legal_transition"
    using legal_transitionI assms(1) .
  have hstar: "(p, apply_move p m) \<in> legal_transition\<^sup>*"
    using r_into_rtrancl hstep .
  show False
    using \<open>dead_position p\<close> hstar assms(2)
    by (simp add: dead_position_def)
qed

definition fifty_move_claimable :: "position \<Rightarrow> bool" where
  "fifty_move_claimable p \<longleftrightarrow> position_halfmove p \<ge> 100"

definition seventy_five_move_draw :: "position \<Rightarrow> bool" where
  "seventy_five_move_draw p \<longleftrightarrow> position_halfmove p \<ge> 150"

definition draw_by_repetition :: "position list \<Rightarrow> bool" where
  "draw_by_repetition hs \<longleftrightarrow> fivefold_repetition hs"

definition kings_only_material :: "position \<Rightarrow> bool" where
  "kings_only_material p \<longleftrightarrow>
    (\<forall>s \<in> set all_squares.
      (case position_board p s of
         Some q \<Rightarrow> piece_kind q = King
       | None \<Rightarrow> True))"

lemma kings_only_material_no_capture:
  "kings_only_material p \<Longrightarrow> pseudo_legal p m \<Longrightarrow>
     \<not> move_is_capture p m"
  by (cases m; auto simp add: kings_only_material_def pseudo_legal_def
      all_squares_set
      normal_pseudo_legal_def destination_friendly_def
      pseudo_legal_promotion_def pseudo_legal_en_passant_def
      move_is_capture_def move_capture_square_def has_piece_def
      split: option.splits if_splits)

definition halfmove_clock_after :: "position \<Rightarrow> move \<Rightarrow> nat" where
  "halfmove_clock_after p m = position_halfmove (apply_move p m)"

lemma halfmove_clock_apply_move:
  "halfmove_clock_after p m =
    (if move_is_pawn p m \<or> move_is_capture p m
     then 0 else position_halfmove p + 1)"
  by (simp add: halfmove_clock_after_def halfmove_clock_apply_move)

end
