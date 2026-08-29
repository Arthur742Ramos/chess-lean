section \<open>Mate-in-two showcase\<close>

theory Chess_Mate_Two
  imports Chess_Examples
begin

definition mate_two_candidate :: position where
  "mate_two_candidate =
    the (parse_fen
      ''kr6/1r1N4/2Q5/8/8/8/8/K7 w - - 0 1'')"

lemma mate_two_candidate_defined:
  "parse_fen
      ''kr6/1r1N4/2Q5/8/8/8/8/K7 w - - 0 1''
    \<noteq> None"
  by eval

definition mate_two_key_position :: position where
  "mate_two_key_position =
    apply_move mate_two_candidate (Normal (D,R7) (C,R5))"

definition mate_two_certificate :: mate_certificate where
  "mate_two_certificate =
    MateAttacker (Normal (D,R7) (C,R5))
      (MateDefender
        [(Normal (A,R8) (A,R7),
           MateAttacker (Normal (C,R6) (A,R6)) MateTerminal),
         (Normal (B,R8) (C,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (D,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (E,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (F,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (G,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (H,R8),
           MateAttacker (Normal (C,R6) (B,R7)) MateTerminal)])"

lemma current_mate_reachable_not_dead:
  assumes "(p,q) \<in> legal_transition\<^sup>*"
    and "current_mate q"
  shows "\<not> dead_position p"
  unfolding dead_position_def
  using assms by blast

lemma mate_two_key_move:
  "legal_move mate_two_candidate (Normal (D,R7) (C,R5))"
  by eval

lemma mate_two_key_king_reply:
  "legal_move mate_two_key_position (Normal (A,R8) (A,R7))"
  by eval

lemma mate_two_key_king_mate:
  "legal_move
     (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
     (Normal (C,R6) (A,R6))"
  by eval

lemma mate_two_key_king_current_mate:
  "current_mate
     (apply_move
       (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
       (Normal (C,R6) (A,R6)))"
  by eval

lemma mate_two_key_reaches_mate:
  "(mate_two_key_position,
     apply_move
       (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
       (Normal (C,R6) (A,R6)))
    \<in> legal_transition\<^sup>*"
proof -
  have h1:
      "(mate_two_key_position,
       apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
      \<in> legal_transition"
    using legal_transitionI mate_two_key_king_reply .
  have h2:
      "(apply_move mate_two_key_position (Normal (A,R8) (A,R7)),
       apply_move
        (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
        (Normal (C,R6) (A,R6)))
      \<in> legal_transition"
    using legal_transitionI mate_two_key_king_mate .
  show ?thesis
    using h1 h2 by (blast intro: rtrancl_into_rtrancl r_into_rtrancl)
qed

lemma mate_two_key_not_dead:
  "\<not> dead_position mate_two_key_position"
  using mate_two_key_reaches_mate mate_two_key_king_current_mate
  by (rule current_mate_reachable_not_dead)

lemma mate_two_candidate_not_dead:
  "\<not> dead_position mate_two_candidate"
proof -
  have hroot:
      "(mate_two_candidate, mate_two_key_position)
        \<in> legal_transition"
    using legal_transitionI mate_two_key_move
    by (simp add: mate_two_key_position_def)
  have hpath:
      "(mate_two_candidate,
       apply_move
        (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
        (Normal (C,R6) (A,R6)))
      \<in> legal_transition\<^sup>*"
    using hroot mate_two_key_reaches_mate
    by (blast intro: rtrancl_trans r_into_rtrancl)
  show ?thesis
    using hpath mate_two_key_king_current_mate
    by (rule current_mate_reachable_not_dead)
qed

lemma legal_move_not_stalemate:
  assumes "legal_move p m"
  shows "\<not> stalemate p"
  using legal_moves_complete[OF assms]
  by (auto simp add: stalemate_def)

lemma mate_two_rook_reply_facts:
  assumes "r = Normal (B,R8) (C,R8) \<or>
            r = Normal (B,R8) (D,R8) \<or>
            r = Normal (B,R8) (E,R8) \<or>
            r = Normal (B,R8) (F,R8) \<or>
            r = Normal (B,R8) (G,R8) \<or>
            r = Normal (B,R8) (H,R8)"
  shows "legal_move mate_two_key_position r \<and>
         legal_move (apply_move mate_two_key_position r)
           (Normal (C,R6) (B,R7)) \<and>
         checkmate
           (apply_move (apply_move mate_two_key_position r)
             (Normal (C,R6) (B,R7))) \<and>
         \<not> seventy_five_move_draw (apply_move mate_two_key_position r)"
  using assms
  by (elim disjE; simp_all; eval)

lemma mate_two_key_replies_complete:
  "set (legal_moves mate_two_key_position) \<subseteq>
    {Normal (A,R8) (A,R7), Normal (B,R8) (C,R8),
     Normal (B,R8) (D,R8), Normal (B,R8) (E,R8),
     Normal (B,R8) (F,R8), Normal (B,R8) (G,R8),
     Normal (B,R8) (H,R8)}"
  by eval

lemma mate_two_key_king_checkmate:
  "checkmate
     (apply_move
       (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
       (Normal (C,R6) (A,R6)))"
  by eval

lemma mate_two_key_no_75:
  "\<not> seventy_five_move_draw mate_two_key_position"
  by eval

lemma mate_two_candidate_no_75:
  "\<not> seventy_five_move_draw mate_two_candidate"
  by eval

lemma mate_two_candidate_turn:
  "position_turn mate_two_candidate = White"
  by eval

lemma mate_two_key_turn:
  "position_turn mate_two_key_position = Black"
  by eval

lemma mate_two_king_reply_no_75:
  "\<not> seventy_five_move_draw
     (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))"
  by eval

lemma mate_two_king_reply_not_dead:
  "\<not> dead_position
     (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))"
  using legal_move_child_current_mate_not_dead
    mate_two_key_king_mate mate_two_key_king_current_mate
  by blast

lemma mate_two_king_reply_turn:
  "position_turn
     (apply_move mate_two_key_position (Normal (A,R8) (A,R7))) = White"
  by (simp add: turn_apply_move mate_two_key_turn)

lemma mate_two_king_final_turn:
  "position_turn
     (apply_move
       (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))
       (Normal (C,R6) (A,R6))) = Black"
  by (simp add: turn_apply_move mate_two_key_turn)

lemma mate_two_rook_reply_turn:
  assumes "r = Normal (B,R8) (C,R8) \<or>
            r = Normal (B,R8) (D,R8) \<or>
            r = Normal (B,R8) (E,R8) \<or>
            r = Normal (B,R8) (F,R8) \<or>
            r = Normal (B,R8) (G,R8) \<or>
            r = Normal (B,R8) (H,R8)"
  shows "position_turn (apply_move mate_two_key_position r) = White"
  using assms
  by (elim disjE; simp_all add: turn_apply_move mate_two_key_turn)

lemma mate_two_rook_final_turn:
  assumes "r = Normal (B,R8) (C,R8) \<or>
            r = Normal (B,R8) (D,R8) \<or>
            r = Normal (B,R8) (E,R8) \<or>
            r = Normal (B,R8) (F,R8) \<or>
            r = Normal (B,R8) (G,R8) \<or>
            r = Normal (B,R8) (H,R8)"
  shows "position_turn
    (apply_move (apply_move mate_two_key_position r)
      (Normal (C,R6) (B,R7))) = Black"
  using assms
  by (elim disjE; simp_all add: turn_apply_move mate_two_key_turn)

lemma mate_two_rook_reply_not_dead:
  assumes "r = Normal (B,R8) (C,R8) \<or>
            r = Normal (B,R8) (D,R8) \<or>
            r = Normal (B,R8) (E,R8) \<or>
            r = Normal (B,R8) (F,R8) \<or>
            r = Normal (B,R8) (G,R8) \<or>
            r = Normal (B,R8) (H,R8)"
  shows "\<not> dead_position (apply_move mate_two_key_position r)"
proof -
  have hfacts:
      "legal_move mate_two_key_position r \<and>
       legal_move (apply_move mate_two_key_position r)
          (Normal (C,R6) (B,R7)) \<and>
       checkmate
          (apply_move (apply_move mate_two_key_position r)
            (Normal (C,R6) (B,R7)))"
    using mate_two_rook_reply_facts[OF assms] by blast
  have hcurrent:
      "current_mate
          (apply_move (apply_move mate_two_key_position r)
            (Normal (C,R6) (B,R7)))"
    using hfacts by (simp add: current_mate_def checkmate_def)
  have hlegal:
      "legal_move (apply_move mate_two_key_position r)
          (Normal (C,R6) (B,R7))"
    using hfacts by blast
  show ?thesis
    using hlegal hcurrent
    by (rule legal_move_child_current_mate_not_dead)
qed

lemma mate_two_rook_C_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (C,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (C,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (C,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (C,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (C,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_D_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (D,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (D,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (D,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (D,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (D,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_E_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (E,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (E,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (E,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (E,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (E,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_F_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (F,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (F,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (F,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (F,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (F,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_G_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (G,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (G,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (G,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (G,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (G,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_H_facts:
  "legal_move mate_two_key_position (Normal (B,R8) (H,R8)) \<and>
   legal_move (apply_move mate_two_key_position (Normal (B,R8) (H,R8)))
      (Normal (C,R6) (B,R7)) \<and>
   \<not> stalemate (apply_move mate_two_key_position (Normal (B,R8) (H,R8))) \<and>
   \<not> seventy_five_move_draw
      (apply_move mate_two_key_position (Normal (B,R8) (H,R8))) \<and>
   checkmate
      (apply_move
       (apply_move mate_two_key_position (Normal (B,R8) (H,R8)))
       (Normal (C,R6) (B,R7)))"
  by eval

lemma mate_two_rook_C_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (C,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (C,R8)"]
  by simp

lemma mate_two_rook_D_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (D,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (D,R8)"]
  by simp

lemma mate_two_rook_E_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (E,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (E,R8)"]
  by simp

lemma mate_two_rook_F_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (F,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (F,R8)"]
  by simp

lemma mate_two_rook_G_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (G,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (G,R8)"]
  by simp

lemma mate_two_rook_H_not_dead:
  "\<not> dead_position
      (apply_move mate_two_key_position (Normal (B,R8) (H,R8)))"
  using mate_two_rook_reply_not_dead[of "Normal (B,R8) (H,R8)"]
  by simp

lemma mate_two_certificate_checked:
  "check_mate_certificate White mate_two_candidate 3
    mate_two_certificate"
proof -
  note hC = mate_two_rook_C_facts
  note hD = mate_two_rook_D_facts
  note hE = mate_two_rook_E_facts
  note hF = mate_two_rook_F_facts
  note hG = mate_two_rook_G_facts
  note hH = mate_two_rook_H_facts
  have hC':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (C,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (C,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (C,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (C,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (C,R8))) (Normal (C,R6) (B,R7)))"
    using hC
    by (simp add: mate_two_key_position_def)
  have hD':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (D,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (D,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (D,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (D,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (D,R8))) (Normal (C,R6) (B,R7)))"
    using hD
    by (simp add: mate_two_key_position_def)
  have hE':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (E,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (E,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (E,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (E,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (E,R8))) (Normal (C,R6) (B,R7)))"
    using hE
    by (simp add: mate_two_key_position_def)
  have hF':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (F,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (F,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (F,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (F,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (F,R8))) (Normal (C,R6) (B,R7)))"
    using hF
    by (simp add: mate_two_key_position_def)
  have hG':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (G,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (G,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (G,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (G,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (G,R8))) (Normal (C,R6) (B,R7)))"
    using hG
    by (simp add: mate_two_key_position_def)
  have hH':
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (H,R8)) \<and>
       legal_move
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (H,R8))) (Normal (C,R6) (B,R7)) \<and>
       \<not> stalemate
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (H,R8))) \<and>
       \<not> seventy_five_move_draw
         (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
           (Normal (B,R8) (H,R8))) \<and>
       checkmate
         (apply_move
           (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
             (Normal (B,R8) (H,R8))) (Normal (C,R6) (B,R7)))"
    using hH
    by (simp add: mate_two_key_position_def)
  have hC6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (C,R8)))"
    using mate_two_rook_C_not_dead
    by (simp add: mate_two_key_position_def)
  have hD6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (D,R8)))"
    using mate_two_rook_D_not_dead
    by (simp add: mate_two_key_position_def)
  have hE6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (E,R8)))"
    using mate_two_rook_E_not_dead
    by (simp add: mate_two_key_position_def)
  have hF6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (F,R8)))"
    using mate_two_rook_F_not_dead
    by (simp add: mate_two_key_position_def)
  have hG6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (G,R8)))"
    using mate_two_rook_G_not_dead
    by (simp add: mate_two_key_position_def)
  have hH6:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (H,R8)))"
    using mate_two_rook_H_not_dead
    by (simp add: mate_two_key_position_def)
  note hC_norm = hC[unfolded mate_two_key_position_def]
  note hD_norm = hD[unfolded mate_two_key_position_def]
  note hE_norm = hE[unfolded mate_two_key_position_def]
  note hF_norm = hF[unfolded mate_two_key_position_def]
  note hG_norm = hG[unfolded mate_two_key_position_def]
  note hH_norm = hH[unfolded mate_two_key_position_def]
  have hroot_stalemate: "\<not> stalemate mate_two_candidate"
    using legal_move_not_stalemate[OF mate_two_key_move] .
  have hcomplete:
      "set (legal_moves
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))) \<subseteq>
        {Normal (A,R8) (A,R7), Normal (B,R8) (C,R8),
         Normal (B,R8) (D,R8), Normal (B,R8) (E,R8),
         Normal (B,R8) (F,R8), Normal (B,R8) (G,R8),
         Normal (B,R8) (H,R8)}"
    using mate_two_key_replies_complete
    by (simp add: mate_two_key_position_def)
  have hking_stalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using legal_move_not_stalemate[OF mate_two_key_king_mate]
    by (simp add: mate_two_key_position_def)
  have hking_dead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using mate_two_king_reply_not_dead
    by (simp add: mate_two_key_position_def)
  have hking_75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using mate_two_king_reply_no_75
    by (simp add: mate_two_key_position_def)
  have hking_move:
      "legal_move
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))
        (Normal (C,R6) (A,R6))"
    using mate_two_key_king_mate
    by (simp add: mate_two_key_position_def)
  have hking_mate:
      "checkmate
        (apply_move
          (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
            (Normal (A,R8) (A,R7)))
          (Normal (C,R6) (A,R6)))"
    using mate_two_key_king_checkmate
    by (simp add: mate_two_key_position_def)
  have hkey_stalemate:
      "\<not> stalemate
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using legal_move_not_stalemate[OF mate_two_key_king_reply]
    by (simp add: mate_two_key_position_def)
  have hkey_dead:
      "\<not> dead_position
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using mate_two_key_not_dead
    by (simp add: mate_two_key_position_def)
  have hkey_75:
      "\<not> seventy_five_move_draw
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using mate_two_key_no_75
    by (simp add: mate_two_key_position_def)
  have hkey_reply:
      "legal_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
        (Normal (A,R8) (A,R7))"
    using mate_two_key_king_reply
    by (simp add: mate_two_key_position_def)
  show ?thesis
    by (simp add: mate_two_certificate_def check_mate_certificate.simps
      certificate_replies_def numeral_eq_Suc
      mate_two_candidate_not_dead mate_two_key_not_dead
      mate_two_king_reply_not_dead mate_two_rook_reply_not_dead
      mate_two_candidate_no_75 mate_two_key_no_75
      mate_two_king_reply_no_75 mate_two_rook_reply_facts
      mate_two_key_replies_complete mate_two_key_move
      mate_two_key_king_reply mate_two_key_king_mate
      mate_two_key_king_checkmate legal_move_not_stalemate
      fivefold_singleton_false turn_apply_move
      mate_two_candidate_turn mate_two_key_turn
      mate_two_king_reply_turn mate_two_king_final_turn
      mate_two_rook_reply_turn mate_two_rook_final_turn
      mate_two_key_position_def
      mate_two_rook_C_facts mate_two_rook_D_facts
      mate_two_rook_E_facts mate_two_rook_F_facts
      mate_two_rook_G_facts mate_two_rook_H_facts
      mate_two_rook_C_not_dead mate_two_rook_D_not_dead
      mate_two_rook_E_not_dead mate_two_rook_F_not_dead
      mate_two_rook_G_not_dead mate_two_rook_H_not_dead
      hC_norm hD_norm hE_norm hF_norm hG_norm hH_norm
      hC6 hD6 hE6 hF6 hG6 hH6
      hroot_stalemate hcomplete hking_stalemate hking_dead hking_75
      hking_move hking_mate hkey_stalemate hkey_dead hkey_75 hkey_reply)
qed

lemma mate_two_candidate_correct:
  "forced_mate_within White mate_two_candidate 3"
  using mate_two_certificate_checked
  by (rule check_mate_certificate_sound)

text \<open>
  The history-aware certificate below is checked against the public
  claim-aware semantics.  The following small lemmas make the finite
  repetition side conditions explicit rather than relying on the legacy
  singleton-history checker.
\<close>

lemma mate_two_key_occurrences_le_length:
  "key_occurrences k hs \<le> length hs"
  by (simp add: key_occurrences_def)

lemma mate_two_fivefold_repetition_le_length:
  "fivefold_repetition hs \<Longrightarrow> 5 \<le> length hs"
proof -
  assume hf: "fivefold_repetition hs"
  show "5 \<le> length hs"
    using hf
      mate_two_key_occurrences_le_length[
        of "repetition_key (last hs)" hs]
    by (cases "rev hs" rule: list.exhaust;
        simp add: fivefold_repetition_def key_occurrences_def
          split: if_splits option.splits)
qed

lemma mate_two_fivefold_history3_false:
  "\<not> fivefold_repetition [p,q,r]"
proof
  assume hf: "fivefold_repetition [p,q,r]"
  have hlen: "5 \<le> length [p,q,r]"
    using mate_two_fivefold_repetition_le_length[OF hf] .
  show False using hlen by simp
qed

lemma mate_two_key_replies_exact:
  "legal_moves mate_two_key_position =
    [Normal (A,R8) (A,R7), Normal (B,R8) (C,R8),
     Normal (B,R8) (D,R8), Normal (B,R8) (E,R8),
     Normal (B,R8) (F,R8), Normal (B,R8) (G,R8),
     Normal (B,R8) (H,R8)]"
  by eval

lemma mate_two_rook_key_not_root:
  assumes hr:
    "r = Normal (B,R8) (C,R8) \<or>
     r = Normal (B,R8) (D,R8) \<or>
     r = Normal (B,R8) (E,R8) \<or>
     r = Normal (B,R8) (F,R8) \<or>
     r = Normal (B,R8) (G,R8) \<or>
     r = Normal (B,R8) (H,R8)"
  shows "repetition_key (apply_move mate_two_key_position r) \<noteq>
    repetition_key mate_two_candidate"
proof
  have hpiece:
      "position_board mate_two_candidate (B,R8) =
        Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>"
    by eval
  have hnot:
      "apply_board mate_two_key_position r (B,R8) \<noteq>
        position_board mate_two_candidate (B,R8)"
    using hr
    by (elim disjE; simp add: mate_two_key_position_def
      apply_board_def board_move_def board_update_def hpiece)
  assume heq:
      "repetition_key (apply_move mate_two_key_position r) =
        repetition_key mate_two_candidate"
  have hboard:
      "rep_board (repetition_key (apply_move mate_two_key_position r)) =
       rep_board (repetition_key mate_two_candidate)"
    using arg_cong[OF heq, of rep_board] .
  have hpoint:
      "rep_board (repetition_key (apply_move mate_two_key_position r))
         (B,R8) =
       rep_board (repetition_key mate_two_candidate) (B,R8)"
    using fun_cong[OF hboard, of "(B,R8)"] .
  have happly:
      "apply_board mate_two_key_position r (B,R8) =
        position_board mate_two_candidate (B,R8)"
    using hpoint by (simp add: repetition_key_def apply_move_def)
  show False using hnot happly by blast
qed

lemma mate_two_child_key_not_key:
  "repetition_key
      (apply_move mate_two_key_position r) \<noteq>
    repetition_key mate_two_key_position"
proof
  assume heq:
      "repetition_key (apply_move mate_two_key_position r) =
        repetition_key mate_two_key_position"
  have hturn:
      "rep_turn (repetition_key (apply_move mate_two_key_position r)) =
       rep_turn (repetition_key mate_two_key_position)"
    using arg_cong[OF heq, of rep_turn] .
  show False
    using hturn
    by (simp add: repetition_key_def apply_move_def
      mate_two_key_turn turn_apply_move)
qed

lemma mate_two_rook_threefold_claim_after_false:
  assumes hr:
    "r = Normal (B,R8) (C,R8) \<or>
     r = Normal (B,R8) (D,R8) \<or>
     r = Normal (B,R8) (E,R8) \<or>
     r = Normal (B,R8) (F,R8) \<or>
     r = Normal (B,R8) (G,R8) \<or>
     r = Normal (B,R8) (H,R8)"
  shows "\<not> threefold_claimable_after
    [mate_two_candidate, mate_two_key_position] r"
proof -
  have hroot:
      "repetition_key (apply_move mate_two_key_position r) \<noteq>
        repetition_key mate_two_candidate"
    using mate_two_rook_key_not_root[OF hr] .
  have hkey:
      "repetition_key (apply_move mate_two_key_position r) \<noteq>
        repetition_key mate_two_key_position"
    using mate_two_child_key_not_key .
  have hclock:
      "\<not> 100 \<le> position_halfmove
        (apply_move mate_two_key_position r)"
    using hr
    by (elim disjE; simp_all; eval)
  show ?thesis
    using hroot hkey hclock
    by (simp add: threefold_claimable_after_def key_occurrences_def)
qed

lemma mate_two_rook_fifty_move_claim_after_false:
  assumes hr:
    "r = Normal (B,R8) (C,R8) \<or>
     r = Normal (B,R8) (D,R8) \<or>
     r = Normal (B,R8) (E,R8) \<or>
     r = Normal (B,R8) (F,R8) \<or>
     r = Normal (B,R8) (G,R8) \<or>
     r = Normal (B,R8) (H,R8)"
  shows "\<not> fifty_move_claimable_after mate_two_key_position r"
  using hr
  by (elim disjE; simp_all add: fifty_move_claimable_after_def; eval)

lemma mate_two_rook_claim_after_false:
  assumes hr:
    "r = Normal (B,R8) (C,R8) \<or>
     r = Normal (B,R8) (D,R8) \<or>
     r = Normal (B,R8) (E,R8) \<or>
     r = Normal (B,R8) (F,R8) \<or>
     r = Normal (B,R8) (G,R8) \<or>
     r = Normal (B,R8) (H,R8)"
  shows "\<not> semantic_mate_claim_after
    [mate_two_candidate, mate_two_key_position] r"
proof -
  have h3:
      "\<not> threefold_claimable_after
        [mate_two_candidate, mate_two_key_position] r"
    using mate_two_rook_threefold_claim_after_false[OF hr] .
  have hf:
      "\<not> fifty_move_claimable_after mate_two_key_position r"
    using mate_two_rook_fifty_move_claim_after_false[OF hr] .
  show ?thesis
    using h3 hf
    by (simp add: semantic_mate_claim_after_def history_current_def)
qed

lemma mate_two_king_key_not_root:
  "repetition_key
      (apply_move mate_two_key_position (Normal (A,R8) (A,R7))) \<noteq>
    repetition_key mate_two_candidate"
proof
  assume heq:
      "repetition_key
          (apply_move mate_two_key_position (Normal (A,R8) (A,R7))) =
        repetition_key mate_two_candidate"
  have hboard:
      "rep_board
        (repetition_key
          (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))) =
       rep_board (repetition_key mate_two_candidate)"
    using arg_cong[OF heq, of rep_board] .
  have hpoint:
      "rep_board
        (repetition_key
          (apply_move mate_two_key_position (Normal (A,R8) (A,R7))))
          (A,R8) =
       rep_board (repetition_key mate_two_candidate) (A,R8)"
    using fun_cong[OF hboard, of "(A,R8)"] .
  have hpiece:
      "position_board mate_two_candidate (A,R8) =
        Some \<lparr>piece_color = Black, piece_kind = King\<rparr>"
    by eval
  show False
    using hpoint hpiece
    by (simp add: repetition_key_def mate_two_key_position_def
      apply_move_def apply_board_def board_move_def board_update_def)
qed

lemma mate_two_king_claim_after_false:
  "\<not> semantic_mate_claim_after
    [mate_two_candidate, mate_two_key_position]
      (Normal (A,R8) (A,R7))"
proof -
  have hclock:
      "\<not> 100 \<le> position_halfmove
        (apply_move mate_two_key_position (Normal (A,R8) (A,R7)))"
    by eval
  show ?thesis
    using mate_two_king_key_not_root
      mate_two_child_key_not_key hclock
    by (simp add: semantic_mate_claim_after_def history_current_def
      threefold_claimable_after_def fifty_move_claimable_after_def
      key_occurrences_def mate_two_key_position_def)
qed

lemma mate_two_history_claims:
  "\<not> semantic_mate_claim_current
      [mate_two_candidate, mate_two_key_position] \<and>
   (\<forall>m \<in> set (legal_moves mate_two_key_position).
      \<not> semantic_mate_claim_after
        [mate_two_candidate, mate_two_key_position] m)"
proof -
  have hcurrent:
      "\<not> semantic_mate_claim_current
        [mate_two_candidate,mate_two_key_position]"
  proof
    assume hc: "semantic_mate_claim_current
      [mate_two_candidate,mate_two_key_position]"
    have hocc:
        "key_occurrences (repetition_key mate_two_key_position)
          [mate_two_candidate,mate_two_key_position] \<le> 2"
      using mate_two_key_occurrences_le_length[of
        "repetition_key mate_two_key_position"
        "[mate_two_candidate,mate_two_key_position]"]
      by simp
    have hclock:
        "\<not> fifty_move_claimable mate_two_key_position"
      by eval
    show False
      using hc hocc hclock
      by (simp add: semantic_mate_claim_current_def history_current_def
        threefold_claimable_def fifty_move_claimable_def)
  qed
  have hafter:
      "\<forall>m \<in> set (legal_moves mate_two_key_position).
        \<not> semantic_mate_claim_after
          [mate_two_candidate,mate_two_key_position] m"
  proof
    fix m
    assume hm: "m \<in> set (legal_moves mate_two_key_position)"
    have hcases:
        "m = Normal (A,R8) (A,R7) \<or>
         m = Normal (B,R8) (C,R8) \<or>
         m = Normal (B,R8) (D,R8) \<or>
         m = Normal (B,R8) (E,R8) \<or>
         m = Normal (B,R8) (F,R8) \<or>
         m = Normal (B,R8) (G,R8) \<or>
         m = Normal (B,R8) (H,R8)"
      using hm mate_two_key_replies_exact
      by (auto)
    show "\<not> semantic_mate_claim_after
      [mate_two_candidate,mate_two_key_position] m"
      using hcases
      by (elim disjE;
          simp add: mate_two_king_claim_after_false
            mate_two_rook_claim_after_false)
  qed
  show ?thesis
    using hcurrent hafter
    by (simp add: semantic_mate_claim_current_def
      semantic_mate_claim_after_def history_current_def
      fifty_move_claimable_def fifty_move_claimable_after_def
      threefold_claimable_def threefold_claimable_after_def
      mate_two_key_position_def mate_two_key_replies_exact)
qed

lemma mate_two_history_certificate_checked:
  "check_mate_certificate_history White [mate_two_candidate] 3
    mate_two_certificate"
proof -
  have hroot_stalemate: "\<not> stalemate mate_two_candidate"
    using legal_move_not_stalemate[OF mate_two_key_move] .
  have hkey_stalemate:
      "\<not> stalemate mate_two_key_position"
    using legal_move_not_stalemate[OF mate_two_key_king_reply] .
  have hroot_terminal:
      "\<not> semantic_mate_terminal [mate_two_candidate]"
    by (simp add: semantic_mate_terminal_def history_current_def
      mate_two_candidate_not_dead mate_two_candidate_no_75
      fivefold_singleton_false)
  have hkey_terminal:
      "\<not> semantic_mate_terminal
        [mate_two_candidate,mate_two_key_position]"
  proof -
    have hfive:
      "\<not> fivefold_repetition
          [mate_two_candidate,mate_two_key_position]"
      by (simp add: fivefold_repetition_def key_occurrences_def)
    show ?thesis
      using hfive mate_two_key_not_dead mate_two_key_no_75
      by (simp add: semantic_mate_terminal_def history_current_def)
  qed
  have hkey_five:
      "\<not> fivefold_repetition
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]"
    by (simp add: fivefold_repetition_def key_occurrences_def)
  have hroot_move:
      "legal_move mate_two_candidate
        (Normal (D,R7) (C,R5))"
    using mate_two_key_move .
  have hcert:
      "mate_two_certificate =
        MateAttacker (Normal (D,R7) (C,R5))
          (MateDefender
            [(Normal (A,R8) (A,R7),
                MateAttacker (Normal (C,R6) (A,R6)) MateTerminal),
             (Normal (B,R8) (C,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
             (Normal (B,R8) (D,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
             (Normal (B,R8) (E,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
             (Normal (B,R8) (F,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
             (Normal (B,R8) (G,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
             (Normal (B,R8) (H,R8),
                MateAttacker (Normal (C,R6) (B,R7)) MateTerminal)])"
    by (simp add: mate_two_certificate_def)
  have hlist:
      "legal_moves mate_two_key_position =
        [Normal (A,R8) (A,R7), Normal (B,R8) (C,R8),
         Normal (B,R8) (D,R8), Normal (B,R8) (E,R8),
         Normal (B,R8) (F,R8), Normal (B,R8) (G,R8),
         Normal (B,R8) (H,R8)]"
    using mate_two_key_replies_exact .
  have hclaim:
      "\<not> semantic_mate_claim_current
        [mate_two_candidate,mate_two_key_position]"
    using mate_two_history_claims by blast
  have hclaim':
      "\<not> semantic_mate_claim_current
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]"
    using hclaim
    by (simp add: mate_two_key_position_def)
  have hafter:
      "\<forall>m \<in> set (legal_moves mate_two_key_position).
        \<not> semantic_mate_claim_after
          [mate_two_candidate,mate_two_key_position] m"
    using mate_two_history_claims by blast
  have hafter':
      "\<forall>m \<in> set
        (legal_moves (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))).
        \<not> semantic_mate_claim_after
          [mate_two_candidate,
           apply_move mate_two_candidate (Normal (D,R7) (C,R5))] m"
    using hafter
    by (simp add: mate_two_key_position_def)
  have hCdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (C,R8)))"
    using mate_two_rook_C_not_dead
    by (simp add: mate_two_key_position_def)
  have hDdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (D,R8)))"
    using mate_two_rook_D_not_dead
    by (simp add: mate_two_key_position_def)
  have hEdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (E,R8)))"
    using mate_two_rook_E_not_dead
    by (simp add: mate_two_key_position_def)
  have hFdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (F,R8)))"
    using mate_two_rook_F_not_dead
    by (simp add: mate_two_key_position_def)
  have hGdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (G,R8)))"
    using mate_two_rook_G_not_dead
    by (simp add: mate_two_key_position_def)
  have hHdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (H,R8)))"
    using mate_two_rook_H_not_dead
    by (simp add: mate_two_key_position_def)
  have hC75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (C,R8)))"
    using mate_two_rook_C_facts by (simp add: mate_two_key_position_def)
  have hD75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (D,R8)))"
    using mate_two_rook_D_facts by (simp add: mate_two_key_position_def)
  have hE75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (E,R8)))"
    using mate_two_rook_E_facts by (simp add: mate_two_key_position_def)
  have hF75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (F,R8)))"
    using mate_two_rook_F_facts by (simp add: mate_two_key_position_def)
  have hG75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (G,R8)))"
    using mate_two_rook_G_facts by (simp add: mate_two_key_position_def)
  have hH75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (H,R8)))"
    using mate_two_rook_H_facts by (simp add: mate_two_key_position_def)
  have hCclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (C,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (C,R8)"]
    by (simp add: mate_two_key_position_def)
  have hDclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (D,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (D,R8)"]
    by (simp add: mate_two_key_position_def)
  have hEclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (E,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (E,R8)"]
    by (simp add: mate_two_key_position_def)
  have hFclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (F,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (F,R8)"]
    by (simp add: mate_two_key_position_def)
  have hGclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (G,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (G,R8)"]
    by (simp add: mate_two_key_position_def)
  have hHclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (B,R8) (H,R8))"
    using mate_two_rook_claim_after_false[
      of "Normal (B,R8) (H,R8)"]
    by (simp add: mate_two_key_position_def)
  have hKclaim:
      "\<not> semantic_mate_claim_after
        [mate_two_candidate,
         apply_move mate_two_candidate (Normal (D,R7) (C,R5))]
        (Normal (A,R8) (A,R7))"
    using mate_two_king_claim_after_false
    by (simp add: mate_two_key_position_def)
  have hKdead:
      "\<not> dead_position
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using mate_two_king_reply_not_dead
    by (simp add: mate_two_key_position_def)
  have hK75:
      "\<not> seventy_five_move_draw
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using mate_two_king_reply_no_75
    by (simp add: mate_two_key_position_def)
  have hkey_stalemate':
      "\<not> stalemate
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using hkey_stalemate by (simp add: mate_two_key_position_def)
  have hkey_dead':
      "\<not> dead_position
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using mate_two_key_not_dead by (simp add: mate_two_key_position_def)
  have hkey_75':
      "\<not> seventy_five_move_draw
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))"
    using mate_two_key_no_75 by (simp add: mate_two_key_position_def)
  have hKstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (A,R8) (A,R7)))"
    using legal_move_not_stalemate[OF mate_two_key_king_mate]
    by (simp add: mate_two_key_position_def)
  have hCstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (C,R8)))"
    using mate_two_rook_C_facts by (simp add: mate_two_key_position_def)
  have hDstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (D,R8)))"
    using mate_two_rook_D_facts by (simp add: mate_two_key_position_def)
  have hEstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (E,R8)))"
    using mate_two_rook_E_facts by (simp add: mate_two_key_position_def)
  have hFstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (F,R8)))"
    using mate_two_rook_F_facts by (simp add: mate_two_key_position_def)
  have hGstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (G,R8)))"
    using mate_two_rook_G_facts by (simp add: mate_two_key_position_def)
  have hHstalemate:
      "\<not> stalemate
        (apply_move (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
          (Normal (B,R8) (H,R8)))"
    using mate_two_rook_H_facts by (simp add: mate_two_key_position_def)
  have hcert_replies:
      "certificate_replies
        (apply_move mate_two_candidate (Normal (D,R7) (C,R5)))
        [(Normal (A,R8) (A,R7),
            MateAttacker (Normal (C,R6) (A,R6)) MateTerminal),
         (Normal (B,R8) (C,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (D,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (E,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (F,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (G,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal),
         (Normal (B,R8) (H,R8),
            MateAttacker (Normal (C,R6) (B,R7)) MateTerminal)]"
    using hlist
    by (simp add: certificate_replies_def mate_two_key_position_def)
  show ?thesis
    unfolding check_mate_certificate_history_def
    by (simp add: check_mate_certificate_policy.simps
      history_current_def hcert
      hroot_stalemate hkey_stalemate hroot_terminal hkey_terminal hkey_five
      hroot_move hlist hclaim hafter hclaim' hafter'
      hCdead hDdead hEdead hFdead hGdead hHdead
      hC75 hD75 hE75 hF75 hG75 hH75
      hCclaim hDclaim hEclaim hFclaim hGclaim hHclaim hKclaim
      hKdead hK75 hcert_replies
      hkey_stalemate' hkey_dead' hkey_75' hKstalemate
      hCstalemate hDstalemate hEstalemate hFstalemate hGstalemate hHstalemate
      mate_two_candidate_not_dead mate_two_key_not_dead
      mate_two_king_reply_not_dead mate_two_rook_reply_not_dead
      mate_two_candidate_no_75 mate_two_key_no_75
      mate_two_king_reply_no_75 mate_two_rook_reply_facts
      mate_two_key_king_reply mate_two_key_king_mate
      mate_two_key_king_checkmate legal_move_not_stalemate
      mate_two_candidate_turn mate_two_key_turn
      mate_two_king_reply_turn mate_two_king_final_turn
      mate_two_rook_reply_turn mate_two_rook_final_turn
      mate_two_key_position_def
      mate_two_rook_C_facts mate_two_rook_D_facts
      mate_two_rook_E_facts mate_two_rook_F_facts
      mate_two_rook_G_facts mate_two_rook_H_facts
      mate_two_rook_C_not_dead mate_two_rook_D_not_dead
      mate_two_rook_E_not_dead mate_two_rook_F_not_dead
      mate_two_rook_G_not_dead mate_two_rook_H_not_dead
      fivefold_singleton_false mate_two_fivefold_history3_false
      semantic_mate_terminal_def hclaim' hafter'
      turn_apply_move numeral_eq_Suc; eval)
qed

lemma mate_two_candidate_history_correct:
  "forced_mate_within_history White [mate_two_candidate] 3"
  using mate_two_history_certificate_checked
  by (rule check_mate_certificate_history_sound)

end
