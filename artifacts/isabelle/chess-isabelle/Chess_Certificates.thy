section \<open>Mate certificates\<close>

theory Chess_Certificates
  imports Chess_Mate
begin

datatype mate_certificate =
    MateTerminal
  | MateAttacker move mate_certificate
  | MateDefender "(move \<times> mate_certificate) list"

definition certificate_replies ::
    "position \<Rightarrow> (move \<times> mate_certificate) list \<Rightarrow> bool" where
  "certificate_replies p xs \<longleftrightarrow>
    set (legal_moves p) \<subseteq> set (map fst xs)"

fun check_mate_certificate ::
    "color \<Rightarrow> position \<Rightarrow> nat \<Rightarrow> mate_certificate \<Rightarrow> bool" where
  "check_mate_certificate c p n MateTerminal =
     (checkmate p \<and> position_turn p = opponent c)"
| "check_mate_certificate c p 0 (MateAttacker m cert) = False"
| "check_mate_certificate c p (Suc n) (MateAttacker m cert) =
     (position_turn p = c \<and>
       \<not> stalemate p \<and> \<not> dead_position p \<and>
       \<not> fivefold_repetition [p] \<and>
       \<not> seventy_five_move_draw p \<and>
       legal_move p m \<and>
       check_mate_certificate c (apply_move p m) n cert)"
| "check_mate_certificate c p 0 (MateDefender xs) = False"
| "check_mate_certificate c p (Suc n) (MateDefender xs) =
     (position_turn p \<noteq> c \<and>
       \<not> stalemate p \<and> \<not> dead_position p \<and>
       \<not> fivefold_repetition [p] \<and>
       \<not> seventy_five_move_draw p \<and>
       certificate_replies p xs \<and>
       list_all (\<lambda>x. legal_move p (fst x) \<and>
       check_mate_certificate c (apply_move p (fst x)) n (snd x)) xs)"

fun check_mate_certificate_policy ::
    "color \<Rightarrow> (position list \<Rightarrow> bool) \<Rightarrow>
     (position list \<Rightarrow> bool) \<Rightarrow>
     (position list \<Rightarrow> move \<Rightarrow> bool) \<Rightarrow>
     position list \<Rightarrow> nat \<Rightarrow> mate_certificate \<Rightarrow> bool" where
  "check_mate_certificate_policy c terminal claim_current claim_after hs n
      MateTerminal =
     (case history_current hs of
        None \<Rightarrow> False
      | Some p \<Rightarrow> checkmate p \<and> position_turn p = opponent c)"
| "check_mate_certificate_policy c terminal claim_current claim_after hs 0
      (MateAttacker m cert) = False"
| "check_mate_certificate_policy c terminal claim_current claim_after hs
      (Suc n) (MateAttacker m cert) =
     (case history_current hs of
        None \<Rightarrow> False
      | Some p \<Rightarrow>
          position_turn p = c \<and>
          \<not> stalemate p \<and> \<not> terminal hs \<and>
          legal_move p m \<and>
          check_mate_certificate_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n cert)"
| "check_mate_certificate_policy c terminal claim_current claim_after hs 0
      (MateDefender xs) = False"
| "check_mate_certificate_policy c terminal claim_current claim_after hs
      (Suc n) (MateDefender xs) =
     (case history_current hs of
        None \<Rightarrow> False
      | Some p \<Rightarrow>
          position_turn p \<noteq> c \<and>
          \<not> stalemate p \<and> \<not> terminal hs \<and>
          \<not> claim_current hs \<and>
          certificate_replies p xs \<and>
          list_all (\<lambda>x. legal_move p (fst x) \<and>
            \<not> claim_after hs (fst x) \<and>
            check_mate_certificate_policy c terminal claim_current claim_after
              (hs @ [apply_move p (fst x)]) n (snd x)) xs)"

definition check_mate_certificate_history ::
    "color \<Rightarrow> position list \<Rightarrow> nat \<Rightarrow> mate_certificate \<Rightarrow> bool" where
  "check_mate_certificate_history c hs n cert =
     check_mate_certificate_policy c semantic_mate_terminal
       semantic_mate_claim_current semantic_mate_claim_after hs n cert"

lemma certificate_replies_legal_policy:
  assumes "certificate_replies p xs"
    and "m \<in> set (legal_moves p)"
  shows "m \<in> set (map fst xs)"
  using assms by (auto simp add: certificate_replies_def)

lemma check_mate_certificate_policy_sound:
  "check_mate_certificate_policy c terminal claim_current claim_after hs n cert
   \<Longrightarrow>
   forced_mate_within_policy c terminal claim_current claim_after hs n"
proof (induct n arbitrary: hs cert)
  case 0
  then show ?case
    by (cases cert;
        simp add: check_mate_certificate_policy.simps
          forced_mate_within_policy.simps)
next
  case (Suc n)
  show ?case
  proof (cases cert)
    case MateTerminal
    then show ?thesis
      using Suc.prems
      by (cases "history_current hs";
          simp add: check_mate_certificate_policy.simps
            forced_mate_within_policy.simps split: option.splits)
  next
    case (MateAttacker m cert)
    have hsome: "history_current hs \<noteq> None"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate_policy.simps split: option.splits)
    obtain p where hp: "history_current hs = Some p"
      using hsome by (cases "history_current hs"; simp_all)
    have hc:
        "check_mate_certificate_policy c terminal claim_current claim_after
          (hs @ [apply_move p m]) n cert"
      using Suc.prems MateAttacker hp
      by (simp add: check_mate_certificate_policy.simps)
    have hm: "legal_move p m"
      using Suc.prems MateAttacker hp
      by (simp add: check_mate_certificate_policy.simps)
    have hturn: "position_turn p = c"
      using Suc.prems MateAttacker hp
      by (simp add: check_mate_certificate_policy.simps)
    have hstalemate: "\<not> stalemate p"
      using Suc.prems MateAttacker hp
      by (simp add: check_mate_certificate_policy.simps)
    have hterminal: "\<not> terminal hs"
      using Suc.prems MateAttacker hp
      by (simp add: check_mate_certificate_policy.simps)
    have hchild:
        "forced_mate_within_policy c terminal claim_current claim_after
          (hs @ [apply_move p m]) n"
      using Suc.hyps[of "hs @ [apply_move p m]" cert] hc by blast
    have hmem: "m \<in> set (legal_moves p)"
      using hm legal_moves_complete by blast
    have hnotcheck: "\<not> checkmate p"
      using hmem by (auto simp add: checkmate_def)
    have hex:
        "list_ex
          (\<lambda>m. forced_mate_within_policy c terminal claim_current
            claim_after (hs @ [apply_move p m]) n) (legal_moves p)"
      unfolding list_ex_iff
      using hmem hchild by blast
    show ?thesis
      using hp hturn hstalemate hterminal hnotcheck hex
      by (simp add: forced_mate_within_policy.simps)
  next
    case (MateDefender xs)
    have hsome: "history_current hs \<noteq> None"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate_policy.simps split: option.splits)
    obtain p where hp: "history_current hs = Some p"
      using hsome by (cases "history_current hs"; simp_all)
    have hxs: "certificate_replies p xs"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hall:
        "list_all (\<lambda>x. legal_move p (fst x) \<and>
          \<not> claim_after hs (fst x) \<and>
          check_mate_certificate_policy c terminal claim_current claim_after
            (hs @ [apply_move p (fst x)]) n (snd x)) xs"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hturn: "position_turn p \<noteq> c"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hstalemate: "\<not> stalemate p"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hterminal: "\<not> terminal hs"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hclaim: "\<not> claim_current hs"
      using Suc.prems MateDefender hp
      by (simp add: check_mate_certificate_policy.simps)
    have hmate_turn:
        "checkmate p \<Longrightarrow> position_turn p = opponent c"
      using hturn by (cases c; cases "position_turn p"; simp)
    have hchildren:
        "\<forall>m \<in> set (legal_moves p).
          \<not> claim_after hs m \<and>
          forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n"
    proof
      fix m
      assume hm: "m \<in> set (legal_moves p)"
      obtain x where hx: "x \<in> set xs" and hfst: "fst x = m"
        using certificate_replies_legal_policy[OF hxs hm]
        by (auto simp add: in_set_conv_nth)
      have hitem:
          "legal_move p (fst x) \<and> \<not> claim_after hs (fst x) \<and>
           check_mate_certificate_policy c terminal claim_current claim_after
             (hs @ [apply_move p (fst x)]) n (snd x)"
        using hall hx by (auto simp add: list_all_iff)
      have hchild:
          "forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p (fst x)]) n"
        using Suc.hyps[of "hs @ [apply_move p (fst x)]" "snd x"]
          hitem by blast
      show "\<not> claim_after hs m \<and>
          forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n"
        using hitem hchild hfst by simp
    qed
    have hlist:
        "list_all
          (\<lambda>m. \<not> claim_after hs m \<and>
            forced_mate_within_policy c terminal claim_current claim_after
              (hs @ [apply_move p m]) n) (legal_moves p)"
      using hchildren by (simp add: list_all_iff)
    show ?thesis
      using hp hturn hstalemate hterminal hclaim hmate_turn hlist
      by (simp add: forced_mate_within_policy.simps)
  qed
qed

lemma check_mate_certificate_history_sound:
  "check_mate_certificate_history c hs n cert \<Longrightarrow>
   forced_mate_within_history c hs n"
  by (simp add: check_mate_certificate_history_def
      forced_mate_within_history_refinement
      check_mate_certificate_policy_sound)

lemma forced_mate_policy_has_certificate:
  "forced_mate_within_policy c terminal claim_current claim_after hs n
   \<Longrightarrow>
   \<exists>cert. check_mate_certificate_policy c terminal claim_current
     claim_after hs n cert"
proof (induct n arbitrary: hs)
  case 0
  have hcur: "history_current hs \<noteq> None"
    using 0
    by (simp add: forced_mate_within_policy.simps split: option.splits)
  obtain p where hp: "history_current hs = Some p"
    using hcur by (cases "history_current hs"; simp_all)
  have hmate:
      "checkmate p \<and> position_turn p = opponent c"
    using 0 hp
    by (simp add: forced_mate_within_policy.simps)
  show ?case
    by (rule exI[where x = MateTerminal];
        simp add: check_mate_certificate_policy.simps hp hmate)
next
  case (Suc n)
  have hcur: "history_current hs \<noteq> None"
    using Suc.prems
    by (simp add: forced_mate_within_policy.simps split: option.splits)
  obtain p where hp: "history_current hs = Some p"
    using hcur by (cases "history_current hs"; simp_all)
  show ?case
  proof (cases "checkmate p")
    case True
    have hturn: "position_turn p = opponent c"
      using Suc.prems hp True
      by (simp add: forced_mate_within_policy.simps)
    show ?thesis
      by (rule exI[where x = MateTerminal];
          simp add: check_mate_certificate_policy.simps hp True hturn)
  next
    case False
    have hnotcheck: "\<not> checkmate p" using False .
    have hstatus:
        "\<not> stalemate p \<and> \<not> terminal hs"
      using Suc.prems hp hnotcheck
      by (cases "position_turn p = c";
          (simp add: forced_mate_within_policy.simps hnotcheck
             split: if_splits))
    show ?thesis
    proof (cases "position_turn p = c")
      case True
      have hturn: "position_turn p = c" using True .
      have hex:
          "list_ex
            (\<lambda>m. forced_mate_within_policy c terminal claim_current
              claim_after (hs @ [apply_move p m]) n) (legal_moves p)"
        using Suc.prems hp hnotcheck hstatus hturn
        by (simp add: forced_mate_within_policy.simps)
      obtain m where hm: "m \<in> set (legal_moves p)"
        and hchild:
          "forced_mate_within_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n"
        using hex by (auto simp add: list_ex_iff)
      obtain cert where hcert:
          "check_mate_certificate_policy c terminal claim_current claim_after
            (hs @ [apply_move p m]) n cert"
        using Suc.hyps[of "hs @ [apply_move p m]"] hchild by blast
      have hlegal: "legal_move p m"
        using hm legal_moves_sound by blast
      show ?thesis
        by (rule exI[where x = "MateAttacker m cert"];
            simp add: check_mate_certificate_policy.simps hp hturn
              hstatus hlegal hcert)
    next
      case False
      have hturn: "position_turn p \<noteq> c" using False by simp
      have hclaim: "\<not> claim_current hs"
      proof
        assume hc: "claim_current hs"
        have hfalse: "False"
          using Suc.prems hp hnotcheck hstatus hturn hc
          by (simp add: forced_mate_within_policy.simps)
        then show False .
      qed
      have hchildren:
          "\<forall>m \<in> set (legal_moves p).
             \<not> claim_after hs m \<and>
             forced_mate_within_policy c terminal claim_current claim_after
               (hs @ [apply_move p m]) n"
      proof -
        have hpol:
            "list_all
              (\<lambda>m. \<not> claim_after hs m \<and>
                forced_mate_within_policy c terminal claim_current claim_after
                  (hs @ [apply_move p m]) n) (legal_moves p)"
          using Suc.prems hp hnotcheck hstatus hturn hclaim
          by (simp add: forced_mate_within_policy.simps)
        show ?thesis
          using hpol by (simp add: list_all_iff)
      qed
      let ?choice = "\<lambda>m. SOME cert.
        check_mate_certificate_policy c terminal claim_current claim_after
          (hs @ [apply_move p m]) n cert"
      have hchoice:
          "\<forall>m \<in> set (legal_moves p).
             check_mate_certificate_policy c terminal claim_current claim_after
               (hs @ [apply_move p m]) n (?choice m)"
      proof
        fix m
        assume hm: "m \<in> set (legal_moves p)"
        have hchild:
            "forced_mate_within_policy c terminal claim_current claim_after
              (hs @ [apply_move p m]) n"
          using hchildren hm by (auto simp add: list_all_iff)
        have hex:
            "\<exists>cert. check_mate_certificate_policy c terminal
              claim_current claim_after
              (hs @ [apply_move p m]) n cert"
          using Suc.hyps[of "hs @ [apply_move p m]"] hchild by blast
        show "check_mate_certificate_policy c terminal claim_current
            claim_after (hs @ [apply_move p m]) n (?choice m)"
          using someI_ex[OF hex] by (simp add: Let_def)
      qed
      let ?xs = "map (\<lambda>m. (m, ?choice m)) (legal_moves p)"
      have hreply:
          "certificate_replies p ?xs"
        by (simp add: certificate_replies_def)
      have hall:
          "list_all (\<lambda>x. legal_move p (fst x) \<and>
             \<not> claim_after hs (fst x) \<and>
             check_mate_certificate_policy c terminal claim_current claim_after
               (hs @ [apply_move p (fst x)]) n (snd x)) ?xs"
      proof -
        have hall':
            "\<forall>m \<in> set (legal_moves p).
              legal_move p m \<and> \<not> claim_after hs m \<and>
              check_mate_certificate_policy c terminal claim_current claim_after
                (hs @ [apply_move p m]) n (?choice m)"
        proof
          fix m
          assume hm: "m \<in> set (legal_moves p)"
          have hlegal: "legal_move p m"
            using hm legal_moves_sound by blast
          have hclaim_m: "\<not> claim_after hs m"
            using hchildren hm by (auto simp add: list_all_iff)
          have hcert:
              "check_mate_certificate_policy c terminal claim_current claim_after
                (hs @ [apply_move p m]) n (?choice m)"
            using hchoice hm by blast
          show "legal_move p m \<and> \<not> claim_after hs m \<and>
              check_mate_certificate_policy c terminal claim_current claim_after
                (hs @ [apply_move p m]) n (?choice m)"
            using hlegal hclaim_m hcert by blast
        qed
        show ?thesis
          using hall' by (simp add: list_all_iff)
      qed
      show ?thesis
        by (rule exI[where x = "MateDefender ?xs"];
            simp add: check_mate_certificate_policy.simps hp hturn
              hstatus hclaim hreply hall)
    qed
  qed
qed

lemma forced_mate_history_has_certificate:
  "forced_mate_within_history c hs n \<Longrightarrow>
   \<exists>cert. check_mate_certificate_history c hs n cert"
  by (simp add: check_mate_certificate_history_def
      forced_mate_within_history_refinement
      forced_mate_policy_has_certificate)

lemma check_mate_certificate_terminal:
  "check_mate_certificate c p n MateTerminal =
    (checkmate p \<and> position_turn p = opponent c)"
  by (cases n; simp add: check_mate_certificate.simps)

lemma fivefold_singleton_false:
  "\<not> fivefold_repetition [p]"
  by (simp add: fivefold_repetition_def key_occurrences_def)

lemma certificate_replies_legal:
  assumes "certificate_replies p xs"
    and "m \<in> set (legal_moves p)"
  shows "m \<in> set (map fst xs)"
  using assms by (auto simp add: certificate_replies_def)

lemma check_mate_certificate_sound:
  "check_mate_certificate c p n cert \<Longrightarrow>
     forced_mate_within c p n"
proof (induct n arbitrary: p cert)
  case 0
  then show ?case
    by (cases cert; simp add: forced_mate_within_def
        check_mate_certificate.simps)
next
  case (Suc n)
  show ?case
  proof (cases cert)
    case MateTerminal
    then show ?thesis
      using Suc.prems by (simp add: forced_mate_within_def
          check_mate_certificate.simps)
  next
    case (MateAttacker m cert)
    have hc: "check_mate_certificate c (apply_move p m) n cert"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have hm: "legal_move p m"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have hturn: "position_turn p = c"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have hstalemate: "\<not> stalemate p"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have hdead: "\<not> dead_position p"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have h75: "\<not> seventy_five_move_draw p"
      using Suc.prems MateAttacker
      by (simp add: check_mate_certificate.simps)
    have hchild: "forced_mate_within c (apply_move p m) n"
      using Suc.hyps[of "apply_move p m" cert] hc by blast
    have hmem: "m \<in> set (legal_moves p)"
      using hm legal_moves_complete by blast
    have hnotcheck: "\<not> checkmate p"
      using hmem by (auto simp add: checkmate_def)
    have hex:
        "list_ex (\<lambda>m. forced_mate_within c (apply_move p m) n)
           (legal_moves p)"
      unfolding list_ex_iff
      using hmem hchild by blast
    show ?thesis
      using hturn hstalemate hdead h75 hnotcheck hex
      by (simp add: forced_mate_within_def fivefold_singleton_false)
  next
    case (MateDefender xs)
    have hxs: "certificate_replies p xs"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have hall:
        "list_all (\<lambda>x. legal_move p (fst x) \<and>
           check_mate_certificate c (apply_move p (fst x)) n (snd x)) xs"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have hturn: "position_turn p \<noteq> c"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have hstalemate: "\<not> stalemate p"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have hdead: "\<not> dead_position p"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have h75: "\<not> seventy_five_move_draw p"
      using Suc.prems MateDefender
      by (simp add: check_mate_certificate.simps)
    have hmate_turn:
        "checkmate p \<Longrightarrow> position_turn p = opponent c"
      using hturn by (cases c; cases "position_turn p"; simp)
    have hchildren:
        "\<forall>m \<in> set (legal_moves p).
          forced_mate_within c (apply_move p m) n"
    proof
      fix m
      assume hm: "m \<in> set (legal_moves p)"
      obtain x where hx: "x \<in> set xs" and hfst: "fst x = m"
        using certificate_replies_legal[OF hxs hm]
        by (auto simp add: in_set_conv_nth)
      have hcert:
          "check_mate_certificate c (apply_move p (fst x)) n (snd x)"
        using hall hx by (auto simp add: list_all_iff)
      have hforced:
          "forced_mate_within c (apply_move p (fst x)) n"
        using Suc.hyps[of "apply_move p (fst x)" "snd x"] hcert by blast
      show "forced_mate_within c (apply_move p m) n"
        using hforced hfst by simp
    qed
    have hlist:
        "list_all (\<lambda>m. forced_mate_within c (apply_move p m) n)
           (legal_moves p)"
      using hchildren by (simp add: list_all_iff)
    show ?thesis
      using hturn hstalemate hdead h75 hmate_turn hlist
      by (simp add: forced_mate_within_def fivefold_singleton_false)
  qed
qed

definition certificate_choice ::
    "color \<Rightarrow> position \<Rightarrow> nat \<Rightarrow> move \<Rightarrow> mate_certificate" where
  "certificate_choice c p n m =
     (SOME cert. check_mate_certificate c (apply_move p m) n cert)"

lemma certificate_choice_spec:
  assumes "\<exists>cert. check_mate_certificate c (apply_move p m) n cert"
  shows "check_mate_certificate c (apply_move p m) n
      (certificate_choice c p n m)"
  using assms by (simp add: certificate_choice_def someI_ex)

lemma forced_mate_has_certificate:
  "forced_mate_within c p n \<Longrightarrow>
     \<exists>cert. check_mate_certificate c p n cert"
proof (induct n arbitrary: p)
  case 0
  have hp: "checkmate p \<and> position_turn p = opponent c"
    using 0 by simp
  show ?case
    by (rule exI[where x = MateTerminal];
        simp add: check_mate_certificate.simps hp)
next
  case (Suc n)
  show ?case
  proof (cases "checkmate p")
    case True
    have hturn: "position_turn p = opponent c"
      using Suc.prems True by (simp add: forced_mate_within_def)
    show ?thesis
      by (rule exI[where x = MateTerminal];
          simp add: check_mate_certificate.simps True hturn)
  next
    case False
    have hnotcheck: "\<not> checkmate p"
      using False by simp
    have hdraw:
        "\<not> (stalemate p \<or> dead_position p \<or>
          fivefold_repetition [p] \<or> seventy_five_move_draw p)"
    proof
      assume hd: "stalemate p \<or> dead_position p \<or>
          fivefold_repetition [p] \<or> seventy_five_move_draw p"
      have "False"
        using Suc.prems False hd
        by (simp add: forced_mate_within_def)
      then show False .
    qed
    have hstatus:
        "\<not> stalemate p \<and> \<not> dead_position p \<and>
         \<not> fivefold_repetition [p] \<and> \<not> seventy_five_move_draw p"
      using hdraw by blast
    show ?thesis
    proof (cases "position_turn p = c")
      case True
      have hturn: "position_turn p = c" using True .
      have hex:
          "list_ex (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p)"
        using Suc.prems hnotcheck hstatus hturn
        by (simp add: forced_mate_within_def)
      obtain m where hm: "m \<in> set (legal_moves p)"
        and hchild: "forced_mate_within c (apply_move p m) n"
        using hex by (auto simp add: list_ex_iff)
      obtain cert where hcert:
          "check_mate_certificate c (apply_move p m) n cert"
        using Suc.hyps[of "apply_move p m"] hchild by blast
      have hlegal: "legal_move p m"
        using hm legal_moves_sound by blast
      show ?thesis
        by (rule exI[where x = "MateAttacker m cert"];
            simp add: check_mate_certificate.simps hturn hstatus hlegal hcert)
    next
      case False
      have hturn: "position_turn p \<noteq> c" using False by simp
      let ?xs = "map (\<lambda>m. (m, certificate_choice c p n m))
        (legal_moves p)"
      have hall:
          "list_all (\<lambda>m. forced_mate_within c (apply_move p m) n)
             (legal_moves p)"
        using Suc.prems hnotcheck hstatus hturn
        by (simp add: forced_mate_within_def)
      have hexists:
          "\<forall>m \<in> set (legal_moves p). \<exists>cert.
             check_mate_certificate c (apply_move p m) n cert"
      proof
        fix m
        assume hm: "m \<in> set (legal_moves p)"
        have hchild: "forced_mate_within c (apply_move p m) n"
          using hall hm by (auto simp add: list_all_iff)
        have hcert_exists: "\<exists>cert.
            check_mate_certificate c (apply_move p m) n cert"
          using Suc.hyps[of "apply_move p m"] hchild by blast
        show "\<exists>cert.
            check_mate_certificate c (apply_move p m) n cert"
          using hcert_exists .
      qed
      have hforall:
          "\<forall>m \<in> set (legal_moves p). legal_move p m \<and>
             check_mate_certificate c (apply_move p m) n
               (certificate_choice c p n m)"
      proof
        fix m
        assume hm: "m \<in> set (legal_moves p)"
        have hlegal: "legal_move p m"
          using hm legal_moves_sound by blast
        have hm_exists: "\<exists>cert.
            check_mate_certificate c (apply_move p m) n cert"
          using hexists hm by blast
        have hcert:
            "check_mate_certificate c (apply_move p m) n
               (certificate_choice c p n m)"
          using certificate_choice_spec[OF hm_exists] .
        show "legal_move p m \<and>
          check_mate_certificate c (apply_move p m) n
            (certificate_choice c p n m)"
          using hlegal hcert by blast
      qed
      have hchoice:
          "list_all (\<lambda>x. legal_move p (fst x) \<and>
             check_mate_certificate c (apply_move p (fst x)) n (snd x)) ?xs"
        using hforall by (simp add: list_all_iff)
      show ?thesis
        by (rule exI[where x = "MateDefender ?xs"];
            simp add: check_mate_certificate.simps hturn hstatus
              certificate_replies_def hchoice)
    qed
  qed
qed

end
