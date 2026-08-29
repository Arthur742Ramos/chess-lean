section \<open>Canonical Standard Algebraic Notation\<close>

theory Chess_SAN
  imports Chess_Notation Chess_Game Chess_FEN_Text
begin

text \<open>
  SAN is represented as its canonical ASCII string.  Printing is
  position-dependent: legal alternatives determine the minimal source
  disambiguation, and the post-move position determines the check or mate
  suffix.  Parsing accepts exactly one canonical spelling and resolves it
  against the legal move list.
\<close>

type_synonym san = string

definition san_piece_text :: "piece_kind \<Rightarrow> string" where
  "san_piece_text k =
    (case k of
       King \<Rightarrow> [CHR ''K''] | Queen \<Rightarrow> [CHR ''Q''] |
       Rook \<Rightarrow> [CHR ''R''] | Bishop \<Rightarrow> [CHR ''B''] |
       Knight \<Rightarrow> [CHR ''N''] | Pawn \<Rightarrow> [])"

definition san_promotion_text :: "promotion_kind \<Rightarrow> string" where
  "san_promotion_text k =
    (case k of
       PromoteQueen \<Rightarrow> [CHR ''Q''] | PromoteRook \<Rightarrow> [CHR ''R''] |
       PromoteBishop \<Rightarrow> [CHR ''B''] | PromoteKnight \<Rightarrow> [CHR ''N''])"

lemma san_piece_text_injective:
  "san_piece_text k = san_piece_text l \<Longrightarrow> k = l"
  by (cases k; cases l; simp add: san_piece_text_def)

lemma san_promotion_text_injective:
  "san_promotion_text k = san_promotion_text l \<Longrightarrow> k = l"
  by (cases k; cases l; simp add: san_promotion_text_def)

lemma fen_file_char_injective:
  "fen_file_char f = fen_file_char g \<Longrightarrow> f = g"
  by (cases f; cases g; simp add: fen_file_char_def)

lemma fen_file_char_eq_iff:
  "fen_file_char f = fen_file_char g \<longleftrightarrow> f = g"
  by (cases f; cases g; simp add: fen_file_char_def)

lemma fen_rank_char_injective:
  "fen_rank_char r = fen_rank_char s \<Longrightarrow> r = s"
  by (cases r; cases s; simp add: fen_rank_char_def)

lemma fen_rank_char_eq_iff:
  "fen_rank_char r = fen_rank_char s \<longleftrightarrow> r = s"
  by (cases r; cases s; simp add: fen_rank_char_def)

lemma square_eq_iff:
  "s = t \<longleftrightarrow> fst s = fst t \<and> snd s = snd t"
  by (cases s; cases t; simp)

definition san_same_piece :: "position \<Rightarrow> move \<Rightarrow> move \<Rightarrow> bool" where
  "san_same_piece p m n \<longleftrightarrow>
    (case (position_board p (move_source m), position_board p (move_source n)) of
       (Some q, Some q') \<Rightarrow>
         piece_color q = piece_color q' \<and>
         piece_kind q = piece_kind q' \<and>
         piece_kind q \<noteq> Pawn
     | _ \<Rightarrow> False)"

definition san_competing_moves :: "position \<Rightarrow> move \<Rightarrow> move list" where
  "san_competing_moves p m =
    filter (\<lambda>n. n \<noteq> m \<and> \<not> is_castle n \<and>
      move_destination n = move_destination m \<and> san_same_piece p m n)
      (legal_moves p)"

definition san_file_conflict :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "san_file_conflict p m =
    list_ex (\<lambda>n. fst (move_source n) = fst (move_source m))
      (san_competing_moves p m)"

definition san_rank_conflict :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "san_rank_conflict p m =
    list_ex (\<lambda>n. snd (move_source n) = snd (move_source m))
      (san_competing_moves p m)"

definition san_disambiguation_text :: "position \<Rightarrow> move \<Rightarrow> string" where
  "san_disambiguation_text p m =
    (case position_board p (move_source m) of
       Some q \<Rightarrow>
         if piece_kind q = Pawn then []
         else if san_competing_moves p m = [] then []
         else if \<not> san_file_conflict p m
              then [fen_file_char (fst (move_source m))]
         else if \<not> san_rank_conflict p m
              then [fen_rank_char (snd (move_source m))]
         else [fen_file_char (fst (move_source m)),
               fen_rank_char (snd (move_source m))]
     | None \<Rightarrow> [])"

definition san_capture_text :: "position \<Rightarrow> move \<Rightarrow> string" where
  "san_capture_text p m =
    (if move_is_capture p m then [CHR ''x''] else [])"

definition san_destination_text :: "move \<Rightarrow> string" where
  "san_destination_text m =
    [fen_file_char (fst (move_destination m)),
     fen_rank_char (snd (move_destination m))]"

lemma san_destination_text_injective:
  "san_destination_text m = san_destination_text n \<Longrightarrow>
   move_destination m = move_destination n"
  by (cases m; cases n; simp add: san_destination_text_def
      fen_file_char_eq_iff fen_rank_char_eq_iff square_eq_iff
      split: prod.splits)

definition san_pawn_prefix :: "position \<Rightarrow> move \<Rightarrow> string" where
  "san_pawn_prefix p m =
    (case position_board p (move_source m) of
       Some q \<Rightarrow>
         if piece_kind q = Pawn \<and> move_is_capture p m
         then [fen_file_char (fst (move_source m))]
         else []
     | None \<Rightarrow> [])"

definition san_promotion_suffix :: "move \<Rightarrow> string" where
  "san_promotion_suffix m =
    (case move_promotion m of
       None \<Rightarrow> []
     | Some k \<Rightarrow> [CHR ''='', hd (san_promotion_text k)])"

definition san_check_suffix :: "position \<Rightarrow> move \<Rightarrow> string" where
  "san_check_suffix p m =
    (let q = apply_move p m; c = opponent (position_turn p)
     in if checkmate q then [CHR ''#'']
        else if in_check q c then [CHR ''+'']
        else [])"

definition san_non_castle_text :: "position \<Rightarrow> move \<Rightarrow> string" where
  "san_non_castle_text p m =
    (case position_board p (move_source m) of
       Some q \<Rightarrow>
         san_piece_text (piece_kind q) @
         san_pawn_prefix p m @
         san_disambiguation_text p m @
         san_capture_text p m @
         san_destination_text m @
         san_promotion_suffix m
     | None \<Rightarrow> [])"

lemma san_filter_piece_text:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_piece_text k) = san_piece_text k"
  by (cases k; simp add: san_piece_text_def)

lemma san_filter_promotion_text:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_promotion_text k) = san_promotion_text k"
  by (cases k; simp add: san_promotion_text_def)

lemma san_filter_file_char:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      [fen_file_char f] = [fen_file_char f]"
  by (cases f; simp add: fen_file_char_def)

lemma san_filter_rank_char:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      [fen_rank_char r] = [fen_rank_char r]"
  by (cases r; simp add: fen_rank_char_def)

lemma san_filter_capture_char:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      [CHR ''x''] = [CHR ''x'']"
  by simp

lemma san_filter_equals_char:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      [CHR ''=''] = [CHR ''='']"
  by simp

lemma san_promotion_head_not_check:
  "hd (san_promotion_text k) \<noteq> CHR ''+'' \<and>
   hd (san_promotion_text k) \<noteq> CHR ''#''"
  by (cases k; simp add: san_promotion_text_def)

lemma fen_file_char_not_check:
  "fen_file_char f \<noteq> CHR ''+'' \<and> fen_file_char f \<noteq> CHR ''#''"
  by (cases f; simp add: fen_file_char_def)

lemma fen_rank_char_not_check:
  "fen_rank_char r \<noteq> CHR ''+'' \<and> fen_rank_char r \<noteq> CHR ''#''"
  by (cases r; simp add: fen_rank_char_def)

lemma san_filter_pawn_prefix:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_pawn_prefix p m) = san_pawn_prefix p m"
  by (cases "position_board p (move_source m)";
      simp add: san_pawn_prefix_def san_filter_file_char fen_file_char_not_check
        split: option.splits if_splits)

lemma san_filter_disambiguation:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_disambiguation_text p m) = san_disambiguation_text p m"
proof (cases "position_board p (move_source m)")
  case None
  then show ?thesis by (simp add: san_disambiguation_text_def)
next
  case (Some q)
  obtain c k where hq: "q = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases q; simp)
  obtain sf sr where hs: "move_source m = (sf,sr)"
    by (cases "move_source m"; simp)
  show ?thesis
    using Some hq hs
    by (cases k; cases sf; cases sr;
        simp add: san_disambiguation_text_def san_filter_file_char
          san_filter_rank_char fen_file_char_def fen_rank_char_def
          split: if_splits)
qed

lemma san_filter_capture_text:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_capture_text p m) = san_capture_text p m"
  by (simp add: san_capture_text_def split: if_splits)

lemma san_filter_destination_text:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_destination_text m) = san_destination_text m"
  by (simp add: san_destination_text_def san_filter_file_char san_filter_rank_char
      fen_file_char_not_check fen_rank_char_not_check)

lemma san_filter_promotion_suffix:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_promotion_suffix m) = san_promotion_suffix m"
  by (cases m; simp add: san_promotion_suffix_def san_filter_equals_char
      san_filter_promotion_text san_promotion_head_not_check split: option.splits)

lemma san_non_castle_text_no_check:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_non_castle_text p m) = san_non_castle_text p m"
  by (cases "position_board p (move_source m)";
      simp add: san_non_castle_text_def filter_append san_filter_piece_text
        san_filter_pawn_prefix san_filter_disambiguation san_filter_capture_text
        san_filter_destination_text san_filter_promotion_suffix
        split: option.splits)

lemma san_filter_check_suffix:
  "filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'')
      (san_check_suffix p m) = []"
  unfolding san_check_suffix_def
  apply (simp only: Let_def)
  apply (split if_splits)
  by simp_all

definition print_san :: "position \<Rightarrow> move \<Rightarrow> san" where
  "print_san p m =
    (case m of
       WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O''] @ san_check_suffix p m
     | WhiteQueenCastle \<Rightarrow>
         [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O''] @ san_check_suffix p m
     | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O''] @ san_check_suffix p m
     | BlackQueenCastle \<Rightarrow>
         [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O''] @ san_check_suffix p m
     | _ \<Rightarrow> san_non_castle_text p m @ san_check_suffix p m)"

definition san_without_check :: "string \<Rightarrow> string" where
  "san_without_check s = filter (\<lambda>c. c \<noteq> CHR ''+'' \<and> c \<noteq> CHR ''#'') s"

lemma san_without_check_print:
  "san_without_check (print_san p m) =
    (case m of
       WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
     | WhiteQueenCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
     | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
     | BlackQueenCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
     | _ \<Rightarrow> san_non_castle_text p m)"
  by (cases m; simp add: san_without_check_def print_san_def san_filter_check_suffix
      san_non_castle_text_no_check filter_append)

definition parse_san_move :: "position \<Rightarrow> san \<Rightarrow> move option" where
  "parse_san_move p s =
    List.find (\<lambda>m. print_san p m = s) (legal_moves p)"

definition san_disambiguation :: "position \<Rightarrow> move \<Rightarrow> square set" where
  "san_disambiguation p m =
    {move_source n | n. n \<in> set (san_competing_moves p m)}"

text \<open>
  SAN uniqueness is exposed both as a decidable property of the finite
  legal-move list and as a structural theorem for every pair of legal moves.
  The finite predicate remains useful as an executable regression certificate
  for concrete FEN positions; the unconditional legal-move injectivity and
  parse/print round trip below cover arbitrary legal positions without an
  additional uniqueness premise.
\<close>

definition san_unique_on_legal_moves :: "position \<Rightarrow> bool" where
  "san_unique_on_legal_moves p =
    distinct (map (print_san p) (legal_moves p))"

lemma distinct_candidate_moves:
  "distinct candidate_moves"
  by eval

lemma legal_moves_distinct:
  "distinct (legal_moves p)"
  by (simp add: legal_moves_def pseudo_legal_moves_def
      distinct_candidate_moves)

lemma san_unique_on_legal_moves_iff:
  "san_unique_on_legal_moves p \<longleftrightarrow>
   (\<forall>m. m \<in> set (legal_moves p) \<longrightarrow>
      (\<forall>n. n \<in> set (legal_moves p) \<longrightarrow>
        print_san p m = print_san p n \<longrightarrow> m = n))"
  by (simp add: san_unique_on_legal_moves_def distinct_map
      legal_moves_distinct inj_on_def Ball_def)

lemma list_find_unique:
  assumes hm: "m \<in> set xs"
    and hp: "P m"
    and hu: "\<forall>n \<in> set xs. P n \<longrightarrow> n = m"
  shows "List.find P xs = Some m"
proof (cases "List.find P xs" rule: option.exhaust)
  case None
  have hnone: "\<not> (\<exists>x. x \<in> set xs \<and> P x)"
    using find_None_iff[of P xs] None by blast
  have hex: "\<exists>x. x \<in> set xs \<and> P x"
    using hm hp by blast
  with hnone show ?thesis by blast
next
  case (Some x)
  have hx: "x \<in> set xs \<and> P x"
    using Some by (auto simp add: find_Some_iff in_set_conv_nth)
  have hxm: "x = m"
    using hu hx by blast
  then show ?thesis using Some by simp
qed

lemma parse_print_san_legal_move:
  "legal_move p m \<Longrightarrow>
   (\<forall>n. legal_move p n \<and> print_san p n = print_san p m \<longrightarrow> n = m) \<Longrightarrow>
   parse_san_move p (print_san p m) = Some m"
proof -
  assume hm: "legal_move p m"
  assume hu: "\<forall>n. legal_move p n \<and> print_san p n = print_san p m \<longrightarrow> n = m"
  have hm_mem: "m \<in> set (legal_moves p)"
    using legal_moves_complete hm by simp
  have hfind:
      "List.find (\<lambda>n. print_san p n = print_san p m)
         (legal_moves p) = Some m"
    proof (rule list_find_unique[OF hm_mem])
      show "print_san p m = print_san p m" by simp
    next
      show "\<forall>n \<in> set (legal_moves p).
          print_san p n = print_san p m \<longrightarrow> n = m"
      using hu legal_moves_correct by blast
    qed
  show ?thesis
    by (simp add: parse_san_move_def hfind)
qed

lemma parse_print_san_legal_move_checked:
  "san_unique_on_legal_moves p \<Longrightarrow> legal_move p m \<Longrightarrow>
   parse_san_move p (print_san p m) = Some m"
proof -
  assume hu: "san_unique_on_legal_moves p"
  assume hm: "legal_move p m"
  have hm_mem: "m \<in> set (legal_moves p)"
    using legal_moves_complete hm by simp
  have hall:
      "\<forall>n. legal_move p n \<and> print_san p n = print_san p m \<longrightarrow> n = m"
  proof (intro allI impI)
    fix n
    assume hn: "legal_move p n \<and> print_san p n = print_san p m"
    have hn_mem: "n \<in> set (legal_moves p)"
      using legal_moves_complete hn by simp
    have hlist:
        "\<forall>x \<in> set (legal_moves p). \<forall>y \<in> set (legal_moves p).
           print_san p x = print_san p y \<longrightarrow> x = y"
      using hu san_unique_on_legal_moves_iff[of p] by blast
    show "n = m"
      using hlist hn_mem hm_mem hn by blast
  qed
  show ?thesis
    by (rule parse_print_san_legal_move[OF hm hall])
qed

lemma legal_move_source_some:
  "legal_move p m \<Longrightarrow>
   \<exists>q. position_board p (move_source m) = Some q"
proof -
  assume hm: "legal_move p m"
  have hs: "position_board p (move_source m) \<noteq> None"
    using pseudo_legal_source[OF legal_move_pseudo[OF hm]] .
  then show ?thesis by (cases "position_board p (move_source m)"; simp_all)
qed

definition san_last_two :: "string \<Rightarrow> string" where
  "san_last_two xs = drop (length xs - 2) xs"

lemma san_last_two_append:
  "san_last_two (xs @ [a,b]) = [a,b]"
  by (induct xs) (simp_all add: san_last_two_def)

definition san_last_three :: "string \<Rightarrow> string" where
  "san_last_three xs = drop (length xs - 3) xs"

lemma san_last_three_append:
  "san_last_three (xs @ [a,b,c]) = [a,b,c]"
  by (induct xs) (simp_all add: san_last_three_def)

definition san_last_four :: "string \<Rightarrow> string" where
  "san_last_four xs = drop (length xs - 4) xs"

lemma san_last_four_append:
  "san_last_four (xs @ [a,b,c,d]) = [a,b,c,d]"
  by (induct xs) (simp_all add: san_last_four_def)

lemma san_last_two_normal:
  assumes hs: "position_board p s = Some q"
  shows "san_last_two (san_non_castle_text p (Normal s t)) =
    san_destination_text (Normal s t)"
  using hs
  by (simp add: san_non_castle_text_def san_promotion_suffix_def
      san_last_two_def san_destination_text_def append_assoc)

lemma san_last_two_en_passant:
  assumes hs: "position_board p s = Some q"
  shows "san_last_two (san_non_castle_text p (EnPassant s t)) =
    san_destination_text (EnPassant s t)"
  using hs
  by (simp add: san_non_castle_text_def san_promotion_suffix_def
      san_last_two_def san_destination_text_def append_assoc)

lemma san_last_four_promotion:
  assumes hs: "position_board p s = Some q"
  shows "san_last_four (san_non_castle_text p (Promotion s t k)) =
    san_destination_text (Promotion s t k) @
      [CHR ''='', hd (san_promotion_text k)]"
  using hs
proof -
  obtain tf tr where ht: "t = (tf,tr)"
    by (cases t; simp)
  have hbody:
      "san_non_castle_text p (Promotion s t k) =
        san_piece_text (piece_kind q) @ san_pawn_prefix p (Promotion s t k) @
        san_disambiguation_text p (Promotion s t k) @
        san_capture_text p (Promotion s t k) @ san_destination_text (Promotion s t k) @
        [CHR ''='', hd (san_promotion_text k)]"
    by (simp add: san_non_castle_text_def san_promotion_suffix_def hs
        san_destination_text_def)
  have hlast:
      "san_last_four
        ((san_piece_text (piece_kind q) @ san_pawn_prefix p (Promotion s (tf,tr) k) @
          san_disambiguation_text p (Promotion s (tf,tr) k) @
          san_capture_text p (Promotion s (tf,tr) k)) @
         [fen_file_char tf, fen_rank_char tr, CHR ''='', hd (san_promotion_text k)]) =
        [fen_file_char tf, fen_rank_char tr, CHR ''='', hd (san_promotion_text k)]"
    by (rule san_last_four_append)
  show ?thesis
    using hbody ht hlast
    by (simp add: san_destination_text_def append_assoc)
qed

lemma san_competing_member:
  assumes hm: "legal_move p m" and hn: "legal_move p n" and hmn: "m \<noteq> n"
    and hdest: "move_destination m = move_destination n"
    and hpiece: "san_same_piece p m n" and hcastle: "\<not> is_castle n"
  shows "n \<in> set (san_competing_moves p m)"
proof -
  have hnmem: "n \<in> set (legal_moves p)"
    using legal_moves_complete hn by simp
  show ?thesis
    using hnmem hmn hdest hpiece hcastle
    by (simp add: san_competing_moves_def)
qed

definition san_disambiguation_code :: "bool \<Rightarrow> bool \<Rightarrow>
    chess_file \<Rightarrow> rank \<Rightarrow> string" where
  "san_disambiguation_code fc rc f r =
    (if fc then if rc then [fen_file_char f, fen_rank_char r]
     else [fen_rank_char r] else [fen_file_char f])"

lemma fen_file_char_ne_rank_char:
  "fen_file_char f \<noteq> fen_rank_char r"
  by (cases f; cases r; simp add: fen_file_char_def fen_rank_char_def)

lemma fen_rank_char_ne_file_char:
  "fen_rank_char r \<noteq> fen_file_char f"
  by (cases f; cases r; simp add: fen_file_char_def fen_rank_char_def)

lemma san_disambiguation_code_injective:
  assumes heq:
      "san_disambiguation_code fm rm sf sr =
       san_disambiguation_code fn rn tf tr"
    and hfile: "sf = tf \<Longrightarrow> fm \<and> fn"
    and hrank: "sr = tr \<Longrightarrow> rm \<and> rn"
  shows "sf = tf \<and> sr = tr"
  using heq hfile hrank
  by (cases fm; cases rm; cases fn; cases rn;
      simp_all add: san_disambiguation_code_def fen_file_char_eq_iff
        fen_rank_char_eq_iff fen_file_char_ne_rank_char
        fen_rank_char_ne_file_char)

lemma san_disambiguation_source_eq:
  assumes hqm: "position_board p (move_source m) = Some qm"
    and hqn: "position_board p (move_source n) = Some qn"
    and hkind: "piece_kind qm = piece_kind qn"
    and hpawn: "piece_kind qm \<noteq> Pawn"
    and hcm: "san_competing_moves p m \<noteq> []"
    and hcn: "san_competing_moves p n \<noteq> []"
    and hfm: "fst (move_source m) = fst (move_source n) \<Longrightarrow>
       san_file_conflict p m"
    and hfn: "fst (move_source m) = fst (move_source n) \<Longrightarrow>
       san_file_conflict p n"
    and hrm: "snd (move_source m) = snd (move_source n) \<Longrightarrow>
       san_rank_conflict p m"
    and hrn: "snd (move_source m) = snd (move_source n) \<Longrightarrow>
       san_rank_conflict p n"
    and heq: "san_disambiguation_text p m = san_disambiguation_text p n"
  shows "move_source m = move_source n"
proof -
  obtain sf sr where hsm: "move_source m = (sf,sr)"
    by (cases "move_source m"; simp)
  obtain tf tr where hsn: "move_source n = (tf,tr)"
    by (cases "move_source n"; simp)
  have hpawnn: "piece_kind qn \<noteq> Pawn"
    using hkind hpawn by metis
  have hcm': "\<not> san_competing_moves p m = []"
    using hcm by blast
  have hcn': "\<not> san_competing_moves p n = []"
    using hcn by blast
  have hdm:
      "san_disambiguation_text p m =
        (if san_file_conflict p m then
           if san_rank_conflict p m then [fen_file_char sf, fen_rank_char sr]
           else [fen_rank_char sr]
         else [fen_file_char sf])"
    using hqm hpawn hcm' hsm
    by (simp add: san_disambiguation_text_def)
  have hdn:
      "san_disambiguation_text p n =
        (if san_file_conflict p n then
           if san_rank_conflict p n then [fen_file_char tf, fen_rank_char tr]
           else [fen_rank_char tr]
         else [fen_file_char tf])"
    using hqn hpawnn hcn' hsn
    by (simp add: san_disambiguation_text_def)
  have heq':
      "(if san_file_conflict p m then
         if san_rank_conflict p m then [fen_file_char sf, fen_rank_char sr]
         else [fen_rank_char sr]
       else [fen_file_char sf]) =
      (if san_file_conflict p n then
         if san_rank_conflict p n then [fen_file_char tf, fen_rank_char tr]
         else [fen_rank_char tr]
       else [fen_file_char tf])"
    using heq hdm hdn by (simp add: hdm hdn)
  have hcode:
      "san_disambiguation_code (san_file_conflict p m) (san_rank_conflict p m) sf sr =
       san_disambiguation_code (san_file_conflict p n) (san_rank_conflict p n) tf tr"
    using heq'
    by (simp add: san_disambiguation_code_def)
  have hfile:
      "sf = tf \<Longrightarrow> san_file_conflict p m \<and> san_file_conflict p n"
    using hfm hfn hsm hsn by simp
  have hrank:
      "sr = tr \<Longrightarrow> san_rank_conflict p m \<and> san_rank_conflict p n"
    using hrm hrn hsm hsn by simp
  have hst: "sf = tf \<and> sr = tr"
    by (rule san_disambiguation_code_injective[OF hcode hfile hrank])
  show ?thesis
    using hst hsm hsn by simp
qed

lemma san_piece_text_no_O:
  "CHR ''O'' \<notin> set (san_piece_text k)"
  by (cases k; simp add: san_piece_text_def)

lemma san_promotion_text_no_O:
  "CHR ''O'' \<notin> set (san_promotion_text k)"
  by (cases k; simp add: san_promotion_text_def)

lemma san_promotion_head_no_O:
  "CHR ''O'' \<noteq> hd (san_promotion_text k)"
  by (cases k; simp add: san_promotion_text_def)

lemma fen_file_char_no_O:
  "CHR ''O'' \<noteq> fen_file_char f"
  by (cases f; simp add: fen_file_char_def)

lemma fen_rank_char_no_O:
  "CHR ''O'' \<noteq> fen_rank_char r"
  by (cases r; simp add: fen_rank_char_def)

lemma san_disambiguation_text_no_O:
  "CHR ''O'' \<notin> set (san_disambiguation_text p m)"
proof (cases "position_board p (move_source m)")
  case None
  then show ?thesis by (simp add: san_disambiguation_text_def)
next
  case (Some q)
  obtain sf sr where hs: "move_source m = (sf,sr)"
    by (cases "move_source m"; simp)
  show ?thesis
    using Some hs
    by (simp add: san_disambiguation_text_def fen_file_char_no_O
        fen_rank_char_no_O split: if_splits)
qed

lemma san_non_castle_text_no_O:
  assumes hs: "position_board p (move_source m) = Some q"
  shows "CHR ''O'' \<notin> set (san_non_castle_text p m)"
  using hs
  by (simp add: san_non_castle_text_def san_piece_text_no_O san_promotion_text_no_O
      fen_file_char_no_O fen_rank_char_no_O san_pawn_prefix_def
      san_capture_text_def san_destination_text_def san_promotion_suffix_def
      san_promotion_head_no_O san_disambiguation_text_no_O
      split: option.splits if_splits)

lemma fen_file_char_no_x:
  "fen_file_char f \<noteq> CHR ''x''"
  by (cases f; simp add: fen_file_char_def)

lemma fen_rank_char_no_x:
  "fen_rank_char r \<noteq> CHR ''x''"
  by (cases r; simp add: fen_rank_char_def)

lemma san_disambiguation_text_no_x:
  "CHR ''x'' \<notin> set (san_disambiguation_text p m)"
proof (cases "position_board p (move_source m)")
  case None
  then show ?thesis by (simp add: san_disambiguation_text_def)
next
  case (Some q)
  obtain sf sr where hs: "move_source m = (sf,sr)"
    by (cases "move_source m"; simp)
  show ?thesis
    using Some hs
    by (cases sf; cases sr; simp add: san_disambiguation_text_def
        fen_file_char_def fen_rank_char_def split: if_splits)
qed

lemma san_filter_x_disambiguation:
  "filter (\<lambda>c. c = CHR ''x'') (san_disambiguation_text p m) = []"
proof (simp only: filter_empty_conv)
  show "\<forall>x\<in>set (san_disambiguation_text p m). x \<noteq> CHR ''x''"
    using san_disambiguation_text_no_x[of p m] by blast
qed

lemma san_filter_x_capture:
  "filter (\<lambda>c. c = CHR ''x'') (san_capture_text p m) =
   san_capture_text p m"
  by (simp add: san_capture_text_def split: if_splits)

lemma san_disambiguation_capture_eq:
  assumes heq:
    "san_disambiguation_text p m @ san_capture_text p m =
     san_disambiguation_text p n @ san_capture_text p n"
  shows "san_disambiguation_text p m = san_disambiguation_text p n \<and>
    move_is_capture p m = move_is_capture p n"
proof -
  have hfilter:
      "filter (\<lambda>c. c = CHR ''x'')
          (san_disambiguation_text p m @ san_capture_text p m) =
       filter (\<lambda>c. c = CHR ''x'')
          (san_disambiguation_text p n @ san_capture_text p n)"
    using heq by simp
  have hcap: "san_capture_text p m = san_capture_text p n"
    using hfilter by (simp add: filter_append san_filter_x_disambiguation
      san_filter_x_capture)
  have hmove: "move_is_capture p m = move_is_capture p n"
    using hcap by (simp add: san_capture_text_def split: if_splits)
  have hdis: "san_disambiguation_text p m = san_disambiguation_text p n"
    using heq hcap by (simp add: append_eq_append_conv2)
  show ?thesis using hdis hmove by blast
qed

lemma san_normal_nonpawn_fields:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkind: "piece_kind qm = piece_kind qn"
    and hpawn: "piece_kind qm \<noteq> Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "move_destination (Normal s t) = move_destination (Normal u v) \<and>
    move_is_capture p (Normal s t) = move_is_capture p (Normal u v) \<and>
    san_disambiguation_text p (Normal s t) =
      san_disambiguation_text p (Normal u v)"
proof -
  have hlast:
      "san_last_two (san_non_castle_text p (Normal s t)) =
       san_last_two (san_non_castle_text p (Normal u v))"
    using heq by simp
  have hdest_text:
      "san_destination_text (Normal s t) =
       san_destination_text (Normal u v)"
    using hlast san_last_two_normal[OF hqm] san_last_two_normal[OF hqn]
    by simp
  have hdest:
      "move_destination (Normal s t) = move_destination (Normal u v)"
    by (rule san_destination_text_injective[OF hdest_text])
  have hbody_m:
      "san_non_castle_text p (Normal s t) =
       san_piece_text (piece_kind qm) @
       san_disambiguation_text p (Normal s t) @
       san_capture_text p (Normal s t) @
       san_destination_text (Normal s t)"
    using hqm hpawn
    by (simp add: san_non_castle_text_def san_pawn_prefix_def san_promotion_suffix_def)
  have hbody_n:
      "san_non_castle_text p (Normal u v) =
       san_piece_text (piece_kind qn) @
       san_disambiguation_text p (Normal u v) @
       san_capture_text p (Normal u v) @
       san_destination_text (Normal u v)"
    using hqn hkind hpawn
    by (simp add: san_non_castle_text_def san_pawn_prefix_def san_promotion_suffix_def)
  have hpre:
      "(san_piece_text (piece_kind qm) @
          san_disambiguation_text p (Normal s t) @
          san_capture_text p (Normal s t)) @
          san_destination_text (Normal s t) =
       (san_piece_text (piece_kind qn) @
          san_disambiguation_text p (Normal u v) @
          san_capture_text p (Normal u v)) @
          san_destination_text (Normal u v)"
    using heq hbody_m hbody_n by (simp add: append_assoc)
  have hpre0:
      "san_piece_text (piece_kind qm) @
          san_disambiguation_text p (Normal s t) @
          san_capture_text p (Normal s t) =
       san_piece_text (piece_kind qn) @
          san_disambiguation_text p (Normal u v) @
          san_capture_text p (Normal u v)"
    using hpre hdest_text by (simp add: append_assoc)
  have hrest:
      "san_disambiguation_text p (Normal s t) @
          san_capture_text p (Normal s t) =
       san_disambiguation_text p (Normal u v) @
          san_capture_text p (Normal u v)"
    using hpre0 hkind by (simp add: append_assoc)
  have hfields:
      "san_disambiguation_text p (Normal s t) =
          san_disambiguation_text p (Normal u v) \<and>
       move_is_capture p (Normal s t) = move_is_capture p (Normal u v)"
    by (rule san_disambiguation_capture_eq[OF hrest])
  show ?thesis using hdest hfields by blast
qed

lemma legal_move_source_color:
  assumes hm: "legal_move p m"
    and hq: "position_board p (move_source m) = Some q"
  shows "piece_color q = position_turn p"
  using hm hq
  by (cases m;
      simp_all add: legal_move_def pseudo_legal_def normal_pseudo_legal_def
        pseudo_legal_promotion_def pseudo_legal_en_passant_def
        pseudo_legal_castle_def has_piece_def split: option.splits)

lemma san_normal_nonpawn_injective:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkind: "piece_kind qm = piece_kind qn"
    and hpawn: "piece_kind qm \<noteq> Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "Normal s t = Normal u v"
proof (cases "s = u")
  case True
  have hdest:
      "move_destination (Normal s t) = move_destination (Normal u v)"
    using san_normal_nonpawn_fields[OF hm hn hqm hqn hkind hpawn heq]
    by blast
  then show ?thesis using True by simp
next
  case False
  have hcolor_m: "piece_color qm = position_turn p"
  proof (rule legal_move_source_color[of p "Normal s t" qm])
    show "legal_move p (Normal s t)" using hm .
    show "position_board p (move_source (Normal s t)) = Some qm"
      using hqm by simp
  qed
  have hcolor_n: "piece_color qn = position_turn p"
  proof (rule legal_move_source_color[of p "Normal u v" qn])
    show "legal_move p (Normal u v)" using hn .
    show "position_board p (move_source (Normal u v)) = Some qn"
      using hqn by simp
  qed
  have hcm: "san_same_piece p (Normal s t) (Normal u v)"
    using hqm hqn hkind hpawn hcolor_m hcolor_n
    by (simp add: san_same_piece_def)
  have hfields:
      "move_destination (Normal s t) = move_destination (Normal u v) \<and>
       move_is_capture p (Normal s t) = move_is_capture p (Normal u v) \<and>
       san_disambiguation_text p (Normal s t) =
         san_disambiguation_text p (Normal u v)"
    by (rule san_normal_nonpawn_fields[OF hm hn hqm hqn hkind hpawn heq])
  have hdest_fields:
      "move_destination (Normal s t) = move_destination (Normal u v)"
    using hfields by blast
  have hdis_fields:
      "san_disambiguation_text p (Normal s t) =
        san_disambiguation_text p (Normal u v)"
    using hfields by blast
  have hmn: "Normal s t \<noteq> Normal u v"
    using False by simp
  have hmem_m:
      "Normal u v \<in> set (san_competing_moves p (Normal s t))"
  proof (rule san_competing_member[of p "Normal s t" "Normal u v"])
    show "legal_move p (Normal s t)" using hm .
    show "legal_move p (Normal u v)" using hn .
    show "Normal s t \<noteq> Normal u v" using hmn .
    show "move_destination (Normal s t) = move_destination (Normal u v)"
      using hdest_fields .
    show "san_same_piece p (Normal s t) (Normal u v)" using hcm .
    show "\<not> is_castle (Normal u v)" by simp
  qed
  have hcm_rev: "san_same_piece p (Normal u v) (Normal s t)"
    using hqm hqn hkind hpawn hcolor_m hcolor_n
    by (simp add: san_same_piece_def)
  have hmem_n:
      "Normal s t \<in> set (san_competing_moves p (Normal u v))"
  proof (rule san_competing_member[of p "Normal u v" "Normal s t"])
    show "legal_move p (Normal u v)" using hn .
    show "legal_move p (Normal s t)" using hm .
    show "Normal u v \<noteq> Normal s t" using hmn by auto
    show "move_destination (Normal u v) = move_destination (Normal s t)"
      using hdest_fields by simp
    show "san_same_piece p (Normal u v) (Normal s t)" using hcm_rev .
    show "\<not> is_castle (Normal s t)" by simp
  qed
  have hnotnil_m: "san_competing_moves p (Normal s t) \<noteq> []"
    using hmem_m by auto
  have hnotnil_n: "san_competing_moves p (Normal u v) \<noteq> []"
    using hmem_n by auto
  have hfm:
      "fst (move_source (Normal s t)) = fst (move_source (Normal u v))
        \<Longrightarrow> san_file_conflict p (Normal s t)"
    using hmem_m
  proof -
    assume hf:
      "fst (move_source (Normal s t)) = fst (move_source (Normal u v))"
    have hfr:
        "fst (move_source (Normal u v)) = fst (move_source (Normal s t))"
      using hf by simp
    show ?thesis
      unfolding san_file_conflict_def list_ex_iff
      apply (rule bexI[of _ "Normal u v"])
      using hfr apply simp
      using hmem_m by blast
  qed
  have hfn:
      "fst (move_source (Normal s t)) = fst (move_source (Normal u v))
        \<Longrightarrow> san_file_conflict p (Normal u v)"
    using hmem_n
  proof -
    assume hf:
      "fst (move_source (Normal s t)) = fst (move_source (Normal u v))"
    show ?thesis
      unfolding san_file_conflict_def list_ex_iff
      apply (rule bexI[of _ "Normal s t"])
      using hf apply simp
      using hmem_n by blast
  qed
  have hrm:
      "snd (move_source (Normal s t)) = snd (move_source (Normal u v))
        \<Longrightarrow> san_rank_conflict p (Normal s t)"
    using hmem_m
  proof -
    assume hr:
      "snd (move_source (Normal s t)) = snd (move_source (Normal u v))"
    have hrr:
        "snd (move_source (Normal u v)) = snd (move_source (Normal s t))"
      using hr by simp
    show ?thesis
      unfolding san_rank_conflict_def list_ex_iff
      apply (rule bexI[of _ "Normal u v"])
      using hrr apply simp
      using hmem_m by blast
  qed
  have hrn:
      "snd (move_source (Normal s t)) = snd (move_source (Normal u v))
        \<Longrightarrow> san_rank_conflict p (Normal u v)"
    using hmem_n
  proof -
    assume hr:
      "snd (move_source (Normal s t)) = snd (move_source (Normal u v))"
    show ?thesis
      unfolding san_rank_conflict_def list_ex_iff
      apply (rule bexI[of _ "Normal s t"])
      using hr apply simp
      using hmem_n by blast
  qed
  have hqm_move:
      "position_board p (move_source (Normal s t)) = Some qm"
    using hqm by simp
  have hqn_move:
      "position_board p (move_source (Normal u v)) = Some qn"
    using hqn by simp
  have hsource:
      "move_source (Normal s t) = move_source (Normal u v)"
    by (rule san_disambiguation_source_eq[OF hqm_move hqn_move hkind hpawn
      hnotnil_m hnotnil_n hfm hfn hrm hrn hdis_fields])
  show ?thesis using hsource False by simp
qed

lemma pawn_double_single_conflict:
  assumes hd: "pawn_double_geometry c s t"
    and hs: "pawn_move_geometry c u t"
    and hf: "fst s = fst u"
    and hc: "clear_between (position_board p) s t"
    and hpiece: "position_board p u = Some q"
  shows False
proof -
  obtain sf sr where hsr: "s = (sf,sr)" by (cases s; simp)
  obtain uf ur where hur: "u = (uf,ur)" by (cases u; simp)
  obtain tf tr where htr: "t = (tf,tr)" by (cases t; simp)
  have hfile: "sf = uf" using hf hsr hur by simp
  have hbetween: "between s u t"
  proof (cases c)
    case White
    have hds: "sr = R2 \<and> tr = R4 \<and> sf = tf"
      using hd hsr htr White by (simp add: pawn_double_geometry_def)
    have hss: "ur = R3 \<and> uf = tf"
      using hs hsr hur htr hds White
      by (cases ur; simp add: pawn_move_geometry_def rank_index_cases)
    show ?thesis
      using hds hss hfile hsr hur htr
      by (simp add: between_def same_file_def same_rank_def
          same_diagonal_def file_index_def rank_index_def)
  next
    case Black
    have hds: "sr = R7 \<and> tr = R5 \<and> sf = tf"
      using hd hsr htr Black by (simp add: pawn_double_geometry_def)
    have hss: "ur = R6 \<and> uf = tf"
      using hs hsr hur htr hds Black
      by (cases ur; simp add: pawn_move_geometry_def rank_index_cases)
    show ?thesis
      using hds hss hfile hsr hur htr
      by (simp add: between_def same_file_def same_rank_def
          same_diagonal_def file_index_def rank_index_def)
  qed
  have hu_member: "u \<in> set (squares_between s t)"
    using hbetween by (simp add: between_member)
  have hnone: "position_board p u = None"
    using hc hu_member by (simp add: clear_between_def)
  show False using hpiece hnone by simp
qed

lemma move_is_capture_normal_iff:
  "move_is_capture p (Normal s t) \<longleftrightarrow>
    position_board p t \<noteq> None"
  by (simp add: move_is_capture_def move_capture_square_def split: option.splits)

lemma normal_pawn_capture_geometry:
  assumes hm: "legal_move p (Normal s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "move_is_capture p (Normal s t)"
  shows "pawn_attack_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Normal s t)" using legal_move_pseudo[OF hm] .
  have ht: "position_board p t \<noteq> None"
    using hc by (simp add: move_is_capture_normal_iff)
  show ?thesis using hp hq hk ht
    by (auto simp add: pseudo_legal_def normal_pseudo_legal_def normal_piece_geometry_def
      destination_friendly_def split: option.splits if_splits)
qed

lemma normal_pawn_quiet_geometry:
  assumes hm: "legal_move p (Normal s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Normal s t)"
  shows "pawn_move_geometry (position_turn p) s t \<or>
    pawn_double_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Normal s t)" using legal_move_pseudo[OF hm] .
  have ht: "position_board p t = None"
    using hc by (simp add: move_is_capture_normal_iff)
  show ?thesis using hp hq hk ht
    by (auto simp add: pseudo_legal_def normal_pseudo_legal_def normal_piece_geometry_def
      destination_friendly_def split: option.splits if_splits)
qed

lemma normal_pawn_double_clear:
  assumes hm: "legal_move p (Normal s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Normal s t)"
    and hd: "pawn_double_geometry (position_turn p) s t"
  shows "clear_between (position_board p) s t"
proof -
  have hp: "pseudo_legal p (Normal s t)" using legal_move_pseudo[OF hm] .
  have ht: "position_board p t = None"
    using hc by (simp add: move_is_capture_normal_iff)
  have hmd: "\<not> pawn_move_geometry (position_turn p) s t"
    using hd
    by (cases "position_turn p"; cases s; cases t;
        simp add: pawn_move_geometry_def pawn_double_geometry_def rank_index_cases)
  show ?thesis using hp hq hk ht hd
    by (auto simp add: pseudo_legal_def normal_pseudo_legal_def normal_piece_geometry_def hmd
      destination_friendly_def split: option.splits if_splits)
qed

lemma normal_pawn_geometry:
  assumes hm: "legal_move p (Normal s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
  shows "pawn_move_geometry (position_turn p) s t \<or>
    pawn_attack_geometry (position_turn p) s t \<or>
    pawn_double_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Normal s t)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp hq hk
    by (auto simp add: pseudo_legal_def normal_pseudo_legal_def normal_piece_geometry_def
      destination_friendly_def split: option.splits if_splits)
qed

lemma pawn_move_source_rank_eq:
  assumes hm: "pawn_move_geometry c s t"
    and hn: "pawn_move_geometry c u t"
  shows "snd s = snd u"
proof -
  obtain sf sr where hs: "s = (sf,sr)" by (cases s; simp)
  obtain uf ur where hu: "u = (uf,ur)" by (cases u; simp)
  obtain tf tr where ht: "t = (tf,tr)" by (cases t; simp)
  show ?thesis using hm hn hs hu ht
  by (cases c; cases sr; cases ur; cases tr;
      simp add: pawn_move_geometry_def rank_index_cases)
qed

lemma pawn_attack_source_rank_eq:
  assumes hm: "pawn_attack_geometry c s t"
    and hn: "pawn_attack_geometry c u t"
  shows "snd s = snd u"
proof -
  obtain sf sr where hs: "s = (sf,sr)" by (cases s; simp)
  obtain uf ur where hu: "u = (uf,ur)" by (cases u; simp)
  obtain tf tr where ht: "t = (tf,tr)" by (cases t; simp)
  show ?thesis using hm hn hs hu ht
  by (cases c; cases sr; cases ur; cases tr;
      simp add: pawn_attack_geometry_def rank_index_cases)
qed

lemma pawn_move_double_source_rank_eq:
  assumes hm: "pawn_double_geometry c s t"
    and hn: "pawn_double_geometry c u t"
  shows "snd s = snd u"
proof -
  obtain sf sr where hs: "s = (sf,sr)" by (cases s; simp)
  obtain uf ur where hu: "u = (uf,ur)" by (cases u; simp)
  obtain tf tr where ht: "t = (tf,tr)" by (cases t; simp)
  show ?thesis using hm hn hs hu ht
  by (cases c; cases sr; cases ur; cases tr;
      simp add: pawn_double_geometry_def rank_index_cases)
qed

lemma pawn_move_attack_file_conflict:
  assumes hm: "pawn_move_geometry c s t"
    and ha: "pawn_attack_geometry c u t"
    and hf: "fst s = fst u"
  shows False
proof -
  have hst: "fst s = fst t"
    using hm by (simp add: pawn_move_geometry_def)
  have hut: "fst u = fst t"
    using hst hf by simp
  show False
    using ha hut by (simp add: pawn_attack_geometry_def)
qed

lemma pawn_double_attack_file_conflict:
  assumes hd: "pawn_double_geometry c s t"
    and ha: "pawn_attack_geometry c u t"
    and hf: "fst s = fst u"
  shows False
proof -
  have hst: "fst s = fst t"
    using hd by (simp add: pawn_double_geometry_def)
  have hut: "fst u = fst t"
    using hst hf by simp
  show False
    using ha hut by (simp add: pawn_attack_geometry_def)
qed

lemma pawn_normal_source_eq:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hfile: "fst s = fst u"
    and hcap: "move_is_capture p (Normal s t) =
      move_is_capture p (Normal u v)"
  shows "s = u"
proof -
  have hc: "move_is_capture p (Normal s t) \<longrightarrow>
      pawn_attack_geometry (position_turn p) s t"
    using normal_pawn_capture_geometry[OF hm hqm hkm] by blast
  have hc': "move_is_capture p (Normal u v) \<longrightarrow>
      pawn_attack_geometry (position_turn p) u v"
    using normal_pawn_capture_geometry[OF hn hqn hkn] by blast
  have hq: "\<not> move_is_capture p (Normal s t) \<longrightarrow>
      pawn_move_geometry (position_turn p) s t \<or>
      pawn_double_geometry (position_turn p) s t"
    using normal_pawn_quiet_geometry[OF hm hqm hkm] by blast
  have hq': "\<not> move_is_capture p (Normal u v) \<longrightarrow>
      pawn_move_geometry (position_turn p) u v \<or>
      pawn_double_geometry (position_turn p) u v"
    using normal_pawn_quiet_geometry[OF hn hqn hkn] by blast
  show ?thesis
  proof (cases "move_is_capture p (Normal s t)")
    case True
    have hcapn: "move_is_capture p (Normal u v)"
      using hcap True by simp
    have ha: "pawn_attack_geometry (position_turn p) s t"
      using hc True by blast
    have ha': "pawn_attack_geometry (position_turn p) u v"
      using hc' hcapn by blast
    have ha'': "pawn_attack_geometry (position_turn p) u t"
      using ha' hdest by simp
    have hr: "snd s = snd u"
      using ha ha'' by (rule pawn_attack_source_rank_eq)
    show ?thesis using hfile hr by (simp add: square_eq_iff)
  next
    case False
    have hcapn: "\<not> move_is_capture p (Normal u v)"
      using hcap False by simp
    have hq_cases:
        "pawn_move_geometry (position_turn p) s t \<or>
         pawn_double_geometry (position_turn p) s t"
      using hq False by blast
    have hq'_cases:
        "pawn_move_geometry (position_turn p) u v \<or>
         pawn_double_geometry (position_turn p) u v"
      using hq' hcapn by blast
    show ?thesis
    proof (rule disjE[OF hq_cases])
      assume hmgeom: "pawn_move_geometry (position_turn p) s t"
      show ?thesis
      proof (rule disjE[OF hq'_cases])
        assume hmgeom': "pawn_move_geometry (position_turn p) u v"
        have hmgeom'': "pawn_move_geometry (position_turn p) u t"
          using hmgeom' hdest by simp
        have hr: "snd s = snd u"
          using hmgeom hmgeom'' by (rule pawn_move_source_rank_eq)
        show ?thesis using hfile hr by (simp add: square_eq_iff)
      next
        assume hdgeom': "pawn_double_geometry (position_turn p) u v"
        have hdgeom'': "pawn_double_geometry (position_turn p) u t"
          using hdgeom' hdest by simp
        have hclear_uv: "clear_between (position_board p) u v"
          using normal_pawn_double_clear[OF hn hqn hkn hcapn hdgeom'] .
        have hclear: "clear_between (position_board p) u t"
          using hclear_uv hdest by simp
        have hfile': "fst u = fst s"
          using hfile by simp
        have hfalse: False
          using pawn_double_single_conflict[of "position_turn p" u t s p qm,
              OF hdgeom'' hmgeom hfile' hclear hqm] by blast
        then show ?thesis by blast
      qed
    next
      assume hdgeom: "pawn_double_geometry (position_turn p) s t"
      show ?thesis
      proof (rule disjE[OF hq'_cases])
        assume hmgeom': "pawn_move_geometry (position_turn p) u v"
        have hmgeom'': "pawn_move_geometry (position_turn p) u t"
          using hmgeom' hdest by simp
        have hclear: "clear_between (position_board p) s t"
          using normal_pawn_double_clear[OF hm hqm hkm False hdgeom] .
        have hfalse: False
          using pawn_double_single_conflict[OF hdgeom hmgeom'']
            hfile hclear hqn by blast
        then show ?thesis by blast
      next
        assume hdgeom': "pawn_double_geometry (position_turn p) u v"
        have hdgeom'': "pawn_double_geometry (position_turn p) u t"
          using hdgeom' hdest by simp
        have hr: "snd s = snd u"
          using hdgeom hdgeom'' by (rule pawn_move_double_source_rank_eq)
        show ?thesis using hfile hr by (simp add: square_eq_iff)
      qed
    qed
  qed
qed

lemma normal_pawn_source_file_quiet:
  assumes hm: "legal_move p (Normal s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Normal s t)"
  shows "fst s = fst t"
proof -
  have hgeom:
      "pawn_move_geometry (position_turn p) s t \<or>
       pawn_double_geometry (position_turn p) s t"
    using normal_pawn_quiet_geometry[OF hm hq hk hc] .
  show ?thesis
  proof (rule disjE[OF hgeom])
    assume h: "pawn_move_geometry (position_turn p) s t"
    then show ?thesis by (simp add: pawn_move_geometry_def)
  next
    assume h: "pawn_double_geometry (position_turn p) s t"
    then show ?thesis by (simp add: pawn_double_geometry_def)
  qed
qed

lemma normal_pawn_source_file_eq:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hcap: "move_is_capture p (Normal s t) =
      move_is_capture p (Normal u v)"
    and hpref:
      "san_pawn_prefix p (Normal s t) =
       san_pawn_prefix p (Normal u v)"
  shows "fst s = fst u"
proof -
  show ?thesis
  proof (cases "move_is_capture p (Normal s t)")
    case True
    have hcapn: "move_is_capture p (Normal u v)"
      using hcap True by simp
    have hpref': "fen_file_char (fst s) = fen_file_char (fst u)"
      using hpref hqm hqn hkm hkn True hcapn
      by (simp add: san_pawn_prefix_def)
    then show ?thesis using fen_file_char_injective by blast
  next
    case False
    have hcapn: "\<not> move_is_capture p (Normal u v)"
      using hcap False by simp
    have hsfile: "fst s = fst t"
      using normal_pawn_source_file_quiet[OF hm hqm hkm False] .
    have hufile: "fst u = fst v"
      using normal_pawn_source_file_quiet[OF hn hqn hkn hcapn] .
    show ?thesis using hsfile hufile hdest by simp
  qed
qed

lemma san_normal_pawn_fields:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "t = v \<and>
    move_is_capture p (Normal s t) = move_is_capture p (Normal u v) \<and>
    san_pawn_prefix p (Normal s t) =
      san_pawn_prefix p (Normal u v)"
proof -
  have hlast:
      "san_last_two (san_non_castle_text p (Normal s t)) =
       san_last_two (san_non_castle_text p (Normal u v))"
    using heq by simp
  have hdest_text:
      "san_destination_text (Normal s t) =
       san_destination_text (Normal u v)"
    using hlast san_last_two_normal[OF hqm] san_last_two_normal[OF hqn]
    by simp
  have hdest: "t = v"
    using san_destination_text_injective[OF hdest_text] by simp
  have hbody_m:
      "san_non_castle_text p (Normal s t) =
       san_pawn_prefix p (Normal s t) @
       san_capture_text p (Normal s t) @
       san_destination_text (Normal s t)"
    using hqm hkm
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hbody_n:
      "san_non_castle_text p (Normal u v) =
       san_pawn_prefix p (Normal u v) @
       san_capture_text p (Normal u v) @
       san_destination_text (Normal u v)"
    using hqn hkn
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hpre:
      "(san_pawn_prefix p (Normal s t) @
        san_capture_text p (Normal s t)) @
        san_destination_text (Normal s t) =
       (san_pawn_prefix p (Normal u v) @
        san_capture_text p (Normal u v)) @
        san_destination_text (Normal u v)"
    using heq hbody_m hbody_n by (simp add: append_assoc)
  have hpre0:
      "san_pawn_prefix p (Normal s t) @
        san_capture_text p (Normal s t) =
       san_pawn_prefix p (Normal u v) @
        san_capture_text p (Normal u v)"
    using hpre hdest_text by (simp add: append_assoc)
  have hcap:
      "move_is_capture p (Normal s t) =
       move_is_capture p (Normal u v)"
  proof -
    have hfilter:
        "filter (\<lambda>c. c = CHR ''x'')
          (san_pawn_prefix p (Normal s t) @ san_capture_text p (Normal s t)) =
         filter (\<lambda>c. c = CHR ''x'')
          (san_pawn_prefix p (Normal u v) @ san_capture_text p (Normal u v))"
      using hpre0 by simp
    show ?thesis
      using hfilter hqm hqn hkm hkn
      by (simp add: san_pawn_prefix_def filter_append san_capture_text_def
          fen_file_char_no_x split: if_splits)
  qed
  have hpref:
      "san_pawn_prefix p (Normal s t) =
       san_pawn_prefix p (Normal u v)"
  proof -
    have hcst:
        "san_capture_text p (Normal s t) =
         san_capture_text p (Normal u v)"
      using hcap by (simp add: san_capture_text_def)
    show ?thesis using hpre0 hcst by (simp add: append_eq_append_conv2)
  qed
  show ?thesis using hdest hcap hpref by blast
qed

lemma promotion_pawn_geometry:
  assumes hm: "legal_move p (Promotion s t k)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
  shows "pawn_move_geometry (position_turn p) s t \<or>
    pawn_attack_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Promotion s t k)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp hq hk
    by (auto simp add: pseudo_legal_def pseudo_legal_promotion_def
      split: option.splits if_splits)
qed

lemma move_is_capture_promotion_iff:
  "move_is_capture p (Promotion s t k) \<longleftrightarrow>
    position_board p t \<noteq> None"
  by (cases "position_board p t";
      simp add: move_is_capture_def move_capture_square_def split: option.splits)

lemma promotion_pawn_capture_geometry:
  assumes hm: "legal_move p (Promotion s t k)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "move_is_capture p (Promotion s t k)"
  shows "pawn_attack_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Promotion s t k)" using legal_move_pseudo[OF hm] .
  have ht: "position_board p t \<noteq> None"
    using hc by (simp add: move_is_capture_promotion_iff)
  show ?thesis using hp hq hk ht
    by (auto simp add: pseudo_legal_def pseudo_legal_promotion_def
      split: option.splits if_splits)
qed

lemma promotion_pawn_quiet_geometry:
  assumes hm: "legal_move p (Promotion s t k)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Promotion s t k)"
  shows "pawn_move_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (Promotion s t k)" using legal_move_pseudo[OF hm] .
  have ht: "position_board p t = None"
    using hc by (simp add: move_is_capture_promotion_iff)
  show ?thesis using hp hq hk ht
    by (auto simp add: pseudo_legal_def pseudo_legal_promotion_def
      split: option.splits if_splits)
qed

lemma promotion_tail_fields:
  assumes heq:
    "san_destination_text (Promotion s t k) @
       [CHR ''='', hd (san_promotion_text k)] =
     san_destination_text (Promotion u v l) @
       [CHR ''='', hd (san_promotion_text l)]"
  shows "t = v \<and> k = l"
proof -
  obtain tf tr where ht: "t = (tf,tr)" by (cases t; simp)
  obtain uf ur where hu: "u = (uf,ur)" by (cases u; simp)
  show ?thesis using heq ht hu
    by (cases k; cases l; simp add: san_destination_text_def
      san_promotion_text_def fen_file_char_eq_iff fen_rank_char_eq_iff)
qed

lemma promotion_pawn_source_file_quiet:
  assumes hm: "legal_move p (Promotion s t k)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Promotion s t k)"
  shows "fst s = fst t"
proof -
  have h: "pawn_move_geometry (position_turn p) s t"
    using promotion_pawn_quiet_geometry[OF hm hq hk hc] .
  then show ?thesis by (simp add: pawn_move_geometry_def)
qed

lemma promotion_pawn_source_file_eq:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Promotion u v l)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hcap: "move_is_capture p (Promotion s t k) =
      move_is_capture p (Promotion u v l)"
    and hpref:
      "san_pawn_prefix p (Promotion s t k) =
       san_pawn_prefix p (Promotion u v l)"
  shows "fst s = fst u"
proof -
  show ?thesis
  proof (cases "move_is_capture p (Promotion s t k)")
    case True
    have hcapn: "move_is_capture p (Promotion u v l)"
      using hcap True by simp
    have hpref': "fen_file_char (fst s) = fen_file_char (fst u)"
      using hpref hqm hqn hkm hkn True hcapn
      by (simp add: san_pawn_prefix_def)
    then show ?thesis using fen_file_char_injective by blast
  next
    case False
    have hcapn: "\<not> move_is_capture p (Promotion u v l)"
      using hcap False by simp
    have hsfile: "fst s = fst t"
      using promotion_pawn_source_file_quiet[OF hm hqm hkm False] .
    have hufile: "fst u = fst v"
      using promotion_pawn_source_file_quiet[OF hn hqn hkn hcapn] .
    show ?thesis using hsfile hufile hdest by simp
  qed
qed

lemma san_promotion_pawn_fields:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Promotion u v l)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (Promotion u v l)"
  shows "t = v \<and> k = l \<and>
    move_is_capture p (Promotion s t k) =
      move_is_capture p (Promotion u v l) \<and>
    san_pawn_prefix p (Promotion s t k) =
      san_pawn_prefix p (Promotion u v l)"
proof -
  have hlast:
      "san_last_four (san_non_castle_text p (Promotion s t k)) =
       san_last_four (san_non_castle_text p (Promotion u v l))"
    using heq by simp
  have htail:
      "san_destination_text (Promotion s t k) @
         [CHR ''='', hd (san_promotion_text k)] =
       san_destination_text (Promotion u v l) @
         [CHR ''='', hd (san_promotion_text l)]"
    using hlast san_last_four_promotion[OF hqm] san_last_four_promotion[OF hqn]
    by simp
  have hfields:
      "t = v \<and> k = l"
    by (rule promotion_tail_fields[OF htail])
  have hdest: "t = v" using hfields by blast
  have hkind: "k = l" using hfields by blast
  have hbody_m:
      "san_non_castle_text p (Promotion s t k) =
       san_pawn_prefix p (Promotion s t k) @
       san_capture_text p (Promotion s t k) @
       san_destination_text (Promotion s t k) @
       [CHR ''='', hd (san_promotion_text k)]"
    using hqm hkm
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hbody_n:
      "san_non_castle_text p (Promotion u v l) =
       san_pawn_prefix p (Promotion u v l) @
       san_capture_text p (Promotion u v l) @
       san_destination_text (Promotion u v l) @
       [CHR ''='', hd (san_promotion_text l)]"
    using hqn hkn
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hpre:
      "(san_pawn_prefix p (Promotion s t k) @
        san_capture_text p (Promotion s t k)) @
        (san_destination_text (Promotion s t k) @
         [CHR ''='', hd (san_promotion_text k)]) =
       (san_pawn_prefix p (Promotion u v l) @
        san_capture_text p (Promotion u v l)) @
        (san_destination_text (Promotion u v l) @
         [CHR ''='', hd (san_promotion_text l)])"
    using heq hbody_m hbody_n by (simp add: append_assoc)
  have hpre0:
      "san_pawn_prefix p (Promotion s t k) @
        san_capture_text p (Promotion s t k) =
       san_pawn_prefix p (Promotion u v l) @
        san_capture_text p (Promotion u v l)"
    using hpre htail by (simp add: append_assoc)
  have hcap:
      "move_is_capture p (Promotion s t k) =
       move_is_capture p (Promotion u v l)"
  proof -
    have hfilter:
        "filter (\<lambda>c. c = CHR ''x'')
          (san_pawn_prefix p (Promotion s t k) @ san_capture_text p (Promotion s t k)) =
         filter (\<lambda>c. c = CHR ''x'')
          (san_pawn_prefix p (Promotion u v l) @ san_capture_text p (Promotion u v l))"
      using hpre0 by simp
    show ?thesis
      using hfilter hqm hqn hkm hkn
      by (simp add: san_pawn_prefix_def filter_append san_capture_text_def
          fen_file_char_no_x split: if_splits)
  qed
  have hpref:
      "san_pawn_prefix p (Promotion s t k) =
       san_pawn_prefix p (Promotion u v l)"
  proof -
    have hcst:
        "san_capture_text p (Promotion s t k) =
         san_capture_text p (Promotion u v l)"
      using hcap by (simp add: san_capture_text_def)
    show ?thesis using hpre0 hcst by (simp add: append_eq_append_conv2)
  qed
  show ?thesis using hdest hkind hcap hpref by blast
qed

lemma promotion_pawn_source_eq:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Promotion u v l)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hkind: "k = l"
    and hfile: "fst s = fst u"
    and hcap: "move_is_capture p (Promotion s t k) =
      move_is_capture p (Promotion u v l)"
  shows "s = u"
proof -
  show ?thesis
  proof (cases "move_is_capture p (Promotion s t k)")
    case True
    have hcapn: "move_is_capture p (Promotion u v l)"
      using hcap True by simp
    have ha: "pawn_attack_geometry (position_turn p) s t"
      using promotion_pawn_capture_geometry[OF hm hqm hkm True] .
    have ha': "pawn_attack_geometry (position_turn p) u v"
      using promotion_pawn_capture_geometry[OF hn hqn hkn hcapn] .
    have ha'': "pawn_attack_geometry (position_turn p) u t"
      using ha' hdest by simp
    have hr: "snd s = snd u"
      using ha ha'' by (rule pawn_attack_source_rank_eq)
    show ?thesis using hfile hr by (simp add: square_eq_iff)
  next
    case False
    have hcapn: "\<not> move_is_capture p (Promotion u v l)"
      using hcap False by simp
    have hmgeom: "pawn_move_geometry (position_turn p) s t"
      using promotion_pawn_quiet_geometry[OF hm hqm hkm False] .
    have hmgeom': "pawn_move_geometry (position_turn p) u v"
      using promotion_pawn_quiet_geometry[OF hn hqn hkn hcapn] .
    have hmgeom'': "pawn_move_geometry (position_turn p) u t"
      using hmgeom' hdest by simp
    have hr: "snd s = snd u"
      using hmgeom hmgeom'' by (rule pawn_move_source_rank_eq)
    show ?thesis using hfile hr by (simp add: square_eq_iff)
  qed
qed

lemma en_passant_pawn_geometry:
  assumes hm: "legal_move p (EnPassant s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
  shows "pawn_attack_geometry (position_turn p) s t"
proof -
  have hp: "pseudo_legal p (EnPassant s t)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp hq hk
    by (auto simp add: pseudo_legal_def pseudo_legal_en_passant_def
      split: option.splits if_splits)
qed

lemma en_passant_capture:
  assumes hm: "legal_move p (EnPassant s t)"
  shows "move_is_capture p (EnPassant s t)"
proof -
  have hp: "pseudo_legal p (EnPassant s t)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp
    by (auto simp add: pseudo_legal_def pseudo_legal_en_passant_def
      move_is_capture_def move_capture_square_def ep_captured_square_def
      has_piece_def split: option.splits if_splits)
qed

lemma en_passant_source_file:
  assumes hm: "legal_move p (EnPassant s t)"
    and hq: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
  shows "fst s \<noteq> fst t"
proof -
  have h: "pawn_attack_geometry (position_turn p) s t"
    using en_passant_pawn_geometry[OF hm hq hk] .
  obtain sf sr where hs: "s = (sf,sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf,tr)" by (cases t; simp)
  show ?thesis using h hs ht
    by (cases sf; cases tf; simp add: pawn_attack_geometry_def file_index_def)
qed

lemma san_en_passant_fields:
  assumes hm: "legal_move p (EnPassant s t)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and heq: "san_non_castle_text p (EnPassant s t) =
      san_non_castle_text p (EnPassant u v)"
  shows "t = v \<and>
    san_pawn_prefix p (EnPassant s t) =
      san_pawn_prefix p (EnPassant u v)"
proof -
  have hlast:
      "san_last_two (san_non_castle_text p (EnPassant s t)) =
       san_last_two (san_non_castle_text p (EnPassant u v))"
    using heq by simp
  have hdest_text:
      "san_destination_text (EnPassant s t) =
       san_destination_text (EnPassant u v)"
    using hlast san_last_two_en_passant[OF hqm] san_last_two_en_passant[OF hqn]
    by simp
  have hdest: "t = v"
    using san_destination_text_injective[OF hdest_text] by simp
  have hbody_m:
      "san_non_castle_text p (EnPassant s t) =
       san_pawn_prefix p (EnPassant s t) @
       san_capture_text p (EnPassant s t) @
       san_destination_text (EnPassant s t)"
    using hqm hkm
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hbody_n:
      "san_non_castle_text p (EnPassant u v) =
       san_pawn_prefix p (EnPassant u v) @
       san_capture_text p (EnPassant u v) @
       san_destination_text (EnPassant u v)"
    using hqn hkn
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hpre:
      "(san_pawn_prefix p (EnPassant s t) @
        san_capture_text p (EnPassant s t)) @
        san_destination_text (EnPassant s t) =
       (san_pawn_prefix p (EnPassant u v) @
        san_capture_text p (EnPassant u v)) @
        san_destination_text (EnPassant u v)"
    using heq hbody_m hbody_n by (simp add: append_assoc)
  have hpre0:
      "san_pawn_prefix p (EnPassant s t) @
        san_capture_text p (EnPassant s t) =
       san_pawn_prefix p (EnPassant u v) @
        san_capture_text p (EnPassant u v)"
    using hpre hdest_text by (simp add: append_assoc)
  have hcm: "move_is_capture p (EnPassant s t)"
    using en_passant_capture[OF hm] .
  have hcn: "move_is_capture p (EnPassant u v)"
    using en_passant_capture[OF hn] .
  have hcap:
      "san_capture_text p (EnPassant s t) =
       san_capture_text p (EnPassant u v)"
    using hcm hcn by (simp add: san_capture_text_def)
  have hpref:
      "san_pawn_prefix p (EnPassant s t) =
       san_pawn_prefix p (EnPassant u v)"
    using hpre0 hcap by (simp add: append_eq_append_conv2)
  show ?thesis using hdest hpref by blast
qed

lemma en_passant_source_eq:
  assumes hm: "legal_move p (EnPassant s t)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hfile: "fst s = fst u"
  shows "s = u"
proof -
  have ha: "pawn_attack_geometry (position_turn p) s t"
    using en_passant_pawn_geometry[OF hm hqm hkm] .
  have ha': "pawn_attack_geometry (position_turn p) u v"
    using en_passant_pawn_geometry[OF hn hqn hkn] .
  have ha'': "pawn_attack_geometry (position_turn p) u t"
    using ha' hdest by simp
  have hr: "snd s = snd u"
    using ha ha'' by (rule pawn_attack_source_rank_eq)
  show ?thesis using hfile hr by (simp add: square_eq_iff)
qed

lemma san_normal_en_passant_fields:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (EnPassant u v)"
  shows "t = v \<and>
    move_is_capture p (Normal s t) \<and>
    san_pawn_prefix p (Normal s t) =
      san_pawn_prefix p (EnPassant u v)"
proof -
  have hlast:
      "san_last_two (san_non_castle_text p (Normal s t)) =
       san_last_two (san_non_castle_text p (EnPassant u v))"
    using heq by simp
  have hdest_text:
      "san_destination_text (Normal s t) =
       san_destination_text (EnPassant u v)"
    using hlast san_last_two_normal[OF hqm] san_last_two_en_passant[OF hqn]
    by simp
  have hdest: "t = v"
    using san_destination_text_injective[OF hdest_text] by simp
  have hbody_m:
      "san_non_castle_text p (Normal s t) =
       san_pawn_prefix p (Normal s t) @
       san_capture_text p (Normal s t) @
       san_destination_text (Normal s t)"
    using hqm hkm
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hbody_n:
      "san_non_castle_text p (EnPassant u v) =
       san_pawn_prefix p (EnPassant u v) @
       san_capture_text p (EnPassant u v) @
       san_destination_text (EnPassant u v)"
    using hqn hkn
    by (simp add: san_non_castle_text_def san_piece_text_def san_pawn_prefix_def
        san_disambiguation_text_def san_promotion_suffix_def)
  have hpre:
      "(san_pawn_prefix p (Normal s t) @
        san_capture_text p (Normal s t)) @
        san_destination_text (Normal s t) =
       (san_pawn_prefix p (EnPassant u v) @
        san_capture_text p (EnPassant u v)) @
        san_destination_text (EnPassant u v)"
    using heq hbody_m hbody_n by (simp add: append_assoc)
  have hpre0:
      "san_pawn_prefix p (Normal s t) @
        san_capture_text p (Normal s t) =
       san_pawn_prefix p (EnPassant u v) @
        san_capture_text p (EnPassant u v)"
    using hpre hdest_text by (simp add: append_assoc)
  have hcn: "move_is_capture p (EnPassant u v)"
    using en_passant_capture[OF hn] .
  have hfilter:
      "filter (\<lambda>c. c = CHR ''x'')
        (san_pawn_prefix p (Normal s t) @ san_capture_text p (Normal s t)) =
       filter (\<lambda>c. c = CHR ''x'')
        (san_pawn_prefix p (EnPassant u v) @ san_capture_text p (EnPassant u v))"
    using hpre0 by simp
  have hcap: "move_is_capture p (Normal s t)"
    using hfilter hqm hqn hkm hkn hcn
    by (simp add: san_pawn_prefix_def filter_append san_capture_text_def
        fen_file_char_no_x split: if_splits)
  have hcaptext:
      "san_capture_text p (Normal s t) =
       san_capture_text p (EnPassant u v)"
    using hcap hcn by (simp add: san_capture_text_def)
  have hpref:
      "san_pawn_prefix p (Normal s t) =
       san_pawn_prefix p (EnPassant u v)"
    using hpre0 hcaptext by (simp add: append_eq_append_conv2)
  show ?thesis using hdest hcap hpref by blast
qed

lemma normal_en_passant_source_eq:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and hdest: "t = v"
    and hcap: "move_is_capture p (Normal s t)"
    and hfile: "fst s = fst u"
  shows False
proof -
  have ha: "pawn_attack_geometry (position_turn p) s t"
    using normal_pawn_capture_geometry[OF hm hqm hkm hcap] .
  have ha': "pawn_attack_geometry (position_turn p) u v"
    using en_passant_pawn_geometry[OF hn hqn hkn] .
  have ha'': "pawn_attack_geometry (position_turn p) u t"
    using ha' hdest by simp
  have hr: "snd s = snd u"
    using ha ha'' by (rule pawn_attack_source_rank_eq)
  have hsu: "s = u"
    using hfile hr by (simp add: square_eq_iff)
  have hnp: "normal_pseudo_legal p s t"
    using legal_move_pseudo[OF hm] by (simp add: pseudo_legal_def)
  have hep: "pseudo_legal_en_passant p (EnPassant s t)"
    using legal_move_pseudo[OF hn] hsu hdest
    by (simp add: pseudo_legal_def)
  show False using normal_en_passant_pseudo_conflict[OF hnp hep] .
qed

lemma san_piece_text_no_equals:
  "CHR ''='' \<notin> set (san_piece_text k)"
  by (cases k; simp add: san_piece_text_def)

lemma fen_file_char_no_equals:
  "fen_file_char f \<noteq> CHR ''=''"
  by (cases f; simp add: fen_file_char_def)

lemma fen_rank_char_no_equals:
  "fen_rank_char r \<noteq> CHR ''=''"
  by (cases r; simp add: fen_rank_char_def)

lemma equals_ne_fen_file_char:
  "CHR ''='' \<noteq> fen_file_char f"
  by (cases f; simp add: fen_file_char_def)

lemma equals_ne_fen_rank_char:
  "CHR ''='' \<noteq> fen_rank_char r"
  by (cases r; simp add: fen_rank_char_def)

lemma san_disambiguation_text_no_equals:
  "CHR ''='' \<notin> set (san_disambiguation_text p m)"
proof (cases "position_board p (move_source m)")
  case None
  then show ?thesis by (simp add: san_disambiguation_text_def)
next
  case (Some q)
  obtain c k where hq: "q = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases q; simp)
  obtain sf sr where hs: "move_source m = (sf,sr)"
    by (cases "move_source m"; simp)
  show ?thesis using Some hs hq
    by (cases k; cases sf; cases sr;
        auto simp add: san_disambiguation_text_def san_piece_text_no_equals
      fen_file_char_no_equals fen_rank_char_no_equals
      equals_ne_fen_file_char equals_ne_fen_rank_char split: if_splits)
qed

lemma san_nonpromotion_text_no_equals_normal:
  assumes hs: "position_board p s = Some q"
  shows "CHR ''='' \<notin> set (san_non_castle_text p (Normal s t))"
  using hs
  by (auto simp add: san_non_castle_text_def san_piece_text_no_equals
      san_pawn_prefix_def san_disambiguation_text_no_equals
      san_capture_text_def san_destination_text_def
      fen_file_char_no_equals fen_rank_char_no_equals
      equals_ne_fen_file_char equals_ne_fen_rank_char
      san_promotion_suffix_def split: option.splits if_splits)

lemma san_nonpromotion_text_no_equals_en_passant:
  assumes hs: "position_board p s = Some q"
  shows "CHR ''='' \<notin> set (san_non_castle_text p (EnPassant s t))"
  using hs
  by (auto simp add: san_non_castle_text_def san_piece_text_no_equals
      san_pawn_prefix_def san_disambiguation_text_no_equals
      san_capture_text_def san_destination_text_def
      fen_file_char_no_equals fen_rank_char_no_equals
      equals_ne_fen_file_char equals_ne_fen_rank_char
      san_promotion_suffix_def split: option.splits if_splits)

lemma san_nonpawn_head_normal:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q \<noteq> Pawn"
  shows "hd (san_non_castle_text p (Normal s t)) =
    hd (san_piece_text (piece_kind q))"
proof -
  obtain c k where hq: "q = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases q; simp)
  obtain sf sr where hss: "s = (sf,sr)" by (cases s; simp)
  show ?thesis using hs hk hq hss
    by (cases k; simp add: san_non_castle_text_def san_piece_text_def
        san_pawn_prefix_def san_disambiguation_text_def
        san_capture_text_def san_destination_text_def
        san_promotion_suffix_def split: option.splits if_splits)
qed

lemma san_pawn_head_normal_capture:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "move_is_capture p (Normal s t)"
  shows "hd (san_non_castle_text p (Normal s t)) =
    fen_file_char (fst s)"
  using hs hk hc
  by (cases s; simp add: san_non_castle_text_def san_piece_text_def
      san_pawn_prefix_def san_disambiguation_text_def san_capture_text_def
      san_destination_text_def san_promotion_suffix_def)

lemma san_pawn_head_normal_quiet:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Normal s t)"
  shows "hd (san_non_castle_text p (Normal s t)) =
    fen_file_char (fst t)"
  using hs hk hc
  by (cases s; cases t; simp add: san_non_castle_text_def san_piece_text_def
      san_pawn_prefix_def san_disambiguation_text_def san_capture_text_def
      san_destination_text_def san_promotion_suffix_def)

lemma san_nonpawn_head_promotion:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q \<noteq> Pawn"
  shows "hd (san_non_castle_text p (Promotion s t k)) =
    hd (san_piece_text (piece_kind q))"
proof -
  obtain c k' where hq: "q = \<lparr>piece_color = c, piece_kind = k'\<rparr>"
    by (cases q; simp)
  obtain sf sr where hss: "s = (sf,sr)" by (cases s; simp)
  show ?thesis using hs hk hq hss
    by (cases k'; simp add: san_non_castle_text_def san_piece_text_def
        san_pawn_prefix_def san_disambiguation_text_def
        san_capture_text_def san_destination_text_def
        san_promotion_suffix_def split: option.splits if_splits)
qed

lemma san_pawn_head_promotion_capture:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "move_is_capture p (Promotion s t k)"
  shows "hd (san_non_castle_text p (Promotion s t k)) =
    fen_file_char (fst s)"
  using hs hk hc
  by (cases s; simp add: san_non_castle_text_def san_piece_text_def
      san_pawn_prefix_def san_disambiguation_text_def san_capture_text_def
      san_destination_text_def san_promotion_suffix_def)

lemma san_pawn_head_promotion_quiet:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "\<not> move_is_capture p (Promotion s t k)"
  shows "hd (san_non_castle_text p (Promotion s t k)) =
    fen_file_char (fst t)"
  using hs hk hc
  by (cases s; cases t; simp add: san_non_castle_text_def san_piece_text_def
      san_pawn_prefix_def san_disambiguation_text_def san_capture_text_def
      san_destination_text_def san_promotion_suffix_def)

lemma san_nonpawn_head_en_passant:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q \<noteq> Pawn"
  shows "hd (san_non_castle_text p (EnPassant s t)) =
    hd (san_piece_text (piece_kind q))"
proof -
  obtain c k' where hq: "q = \<lparr>piece_color = c, piece_kind = k'\<rparr>"
    by (cases q; simp)
  obtain sf sr where hss: "s = (sf,sr)" by (cases s; simp)
  show ?thesis using hs hk hq hss
    by (cases k'; simp add: san_non_castle_text_def san_piece_text_def
        san_pawn_prefix_def san_disambiguation_text_def
        san_capture_text_def san_destination_text_def
        san_promotion_suffix_def split: option.splits if_splits)
qed

lemma san_pawn_head_en_passant:
  assumes hs: "position_board p s = Some q"
    and hk: "piece_kind q = Pawn"
    and hc: "move_is_capture p (EnPassant s t)"
  shows "hd (san_non_castle_text p (EnPassant s t)) =
    fen_file_char (fst s)"
  using hs hk hc
  by (cases s; simp add: san_non_castle_text_def san_piece_text_def
      san_pawn_prefix_def san_disambiguation_text_def san_capture_text_def
      san_destination_text_def san_promotion_suffix_def)

lemma fen_file_char_ne_san_piece_head:
  assumes hk: "k \<noteq> Pawn"
  shows "fen_file_char f \<noteq> hd (san_piece_text k)"
  using hk
  by (cases f; cases k; simp add: fen_file_char_def san_piece_text_def)

lemma san_normal_nonpawn_kind_eq:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm \<noteq> Pawn"
    and hkn: "piece_kind qn \<noteq> Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "piece_kind qm = piece_kind qn"
proof -
  have hhead:
      "hd (san_non_castle_text p (Normal s t)) =
       hd (san_non_castle_text p (Normal u v))"
    using heq by simp
  have hhead':
      "hd (san_piece_text (piece_kind qm)) =
       hd (san_piece_text (piece_kind qn))"
    using hhead san_nonpawn_head_normal[OF hqm hkm]
      san_nonpawn_head_normal[OF hqn hkn] by simp
  have hpiece:
      "san_piece_text (piece_kind qm) =
       san_piece_text (piece_kind qn)"
    using hhead' hkm hkn by (cases "piece_kind qm"; cases "piece_kind qn";
      simp add: san_piece_text_def)
  show ?thesis using san_piece_text_injective hpiece by blast
qed

lemma san_normal_pawn_nonpawn_conflict:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn \<noteq> Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows False
proof -
  have hhead:
      "hd (san_non_castle_text p (Normal s t)) =
       hd (san_non_castle_text p (Normal u v))"
    using heq by simp
  show False
  proof (cases "move_is_capture p (Normal s t)")
    case True
    have hphead:
        "hd (san_non_castle_text p (Normal s t)) =
         fen_file_char (fst s)"
      using san_pawn_head_normal_capture[OF hqm hkm True] .
    have hnhead:
        "hd (san_non_castle_text p (Normal u v)) =
         hd (san_piece_text (piece_kind qn))"
      using san_nonpawn_head_normal[OF hqn hkn] .
    have hfeq:
        "fen_file_char (fst s) =
         hd (san_piece_text (piece_kind qn))"
      using hhead hphead hnhead by simp
    show False
      using fen_file_char_ne_san_piece_head[OF hkn] hfeq by blast
  next
    case False
    have hphead:
        "hd (san_non_castle_text p (Normal s t)) =
         fen_file_char (fst t)"
      using san_pawn_head_normal_quiet[OF hqm hkm False] .
    have hnhead:
        "hd (san_non_castle_text p (Normal u v)) =
         hd (san_piece_text (piece_kind qn))"
      using san_nonpawn_head_normal[OF hqn hkn] .
    have hfeq:
        "fen_file_char (fst t) =
         hd (san_piece_text (piece_kind qn))"
      using hhead hphead hnhead by simp
    show False
      using fen_file_char_ne_san_piece_head[OF hkn] hfeq by blast
  qed
qed

lemma san_normal_pawn_pawn_injective:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm = Pawn"
    and hkn: "piece_kind qn = Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "Normal s t = Normal u v"
proof -
  have hf:
      "t = v \<and>
       move_is_capture p (Normal s t) = move_is_capture p (Normal u v) \<and>
       san_pawn_prefix p (Normal s t) =
         san_pawn_prefix p (Normal u v)"
    by (rule san_normal_pawn_fields[OF hm hn hqm hqn hkm hkn heq])
  have hdest: "t = v" using hf by blast
  have hcap: "move_is_capture p (Normal s t) =
      move_is_capture p (Normal u v)" using hf by blast
  have hpref: "san_pawn_prefix p (Normal s t) =
      san_pawn_prefix p (Normal u v)" using hf by blast
  have hfile:
      "fst s = fst u"
    by (rule normal_pawn_source_file_eq[OF hm hn hqm hqn hkm hkn
      hdest hcap hpref])
  have hsource:
      "s = u"
    by (rule pawn_normal_source_eq[OF hm hn hqm hqn hkm hkn
      hdest hfile hcap])
  show ?thesis using hsource hdest by simp
qed

lemma san_normal_nonpawn_nonpawn_injective:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and hkm: "piece_kind qm \<noteq> Pawn"
    and hkn: "piece_kind qn \<noteq> Pawn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "Normal s t = Normal u v"
proof -
  have hkind: "piece_kind qm = piece_kind qn"
    by (rule san_normal_nonpawn_kind_eq[OF hm hn hqm hqn hkm hkn heq])
  show ?thesis
    by (rule san_normal_nonpawn_injective[OF hm hn hqm hqn hkind hkm heq])
qed

lemma promotion_source_pawn:
  assumes hm: "legal_move p (Promotion s t k)"
    and hq: "position_board p s = Some q"
  shows "piece_kind q = Pawn"
proof -
  have hp: "pseudo_legal p (Promotion s t k)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp hq
    by (simp add: pseudo_legal_def pseudo_legal_promotion_def split: option.splits)
qed

lemma san_promotion_has_equals:
  assumes hs: "position_board p s = Some q"
  shows "CHR ''='' \<in> set (san_non_castle_text p (Promotion s t k))"
  using hs
  by (simp add: san_non_castle_text_def san_promotion_suffix_def
      san_promotion_text_def split: option.splits)

lemma san_noncastle_ne_castle_king:
  assumes hs: "position_board p (move_source m) = Some q"
  shows "san_non_castle_text p m \<noteq> [CHR ''O'', CHR ''-'', CHR ''O'']"
proof
  assume heq: "san_non_castle_text p m = [CHR ''O'', CHR ''-'', CHR ''O'']"
  have hmem: "CHR ''O'' \<in> set (san_non_castle_text p m)"
    using heq by simp
  show False using san_non_castle_text_no_O[OF hs] hmem by blast
qed

lemma san_noncastle_ne_castle_queen:
  assumes hs: "position_board p (move_source m) = Some q"
  shows "san_non_castle_text p m \<noteq>
    [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
proof
  assume heq: "san_non_castle_text p m =
    [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
  have hmem: "CHR ''O'' \<in> set (san_non_castle_text p m)"
    using heq by simp
  show False using san_non_castle_text_no_O[OF hs] hmem by blast
qed

lemma castle_white_turn:
  assumes hm: "legal_move p c"
    and hc: "c = WhiteKingCastle \<or> c = WhiteQueenCastle"
  shows "position_turn p = White"
  using hm hc
  by (cases c; auto simp add: legal_move_def pseudo_legal_def
      pseudo_legal_castle_def split: option.splits if_splits)

lemma castle_black_turn:
  assumes hm: "legal_move p c"
    and hc: "c = BlackKingCastle \<or> c = BlackQueenCastle"
  shows "position_turn p = Black"
  using hm hc
  by (cases c; auto simp add: legal_move_def pseudo_legal_def
      pseudo_legal_castle_def split: option.splits if_splits)

lemma san_promotion_promotion_injective:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Promotion u v l)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (Promotion u v l)"
  shows "Promotion s t k = Promotion u v l"
proof -
  have hkm: "piece_kind qm = Pawn"
    using promotion_source_pawn[OF hm hqm] .
  have hkn: "piece_kind qn = Pawn"
    using promotion_source_pawn[OF hn hqn] .
  have hf:
      "t = v \<and> k = l \<and>
       move_is_capture p (Promotion s t k) =
         move_is_capture p (Promotion u v l) \<and>
       san_pawn_prefix p (Promotion s t k) =
         san_pawn_prefix p (Promotion u v l)"
    by (rule san_promotion_pawn_fields[OF hm hn hqm hqn hkm hkn heq])
  have hdest: "t = v" using hf by blast
  have hkind: "k = l" using hf by blast
  have hcap: "move_is_capture p (Promotion s t k) =
      move_is_capture p (Promotion u v l)" using hf by blast
  have hpref: "san_pawn_prefix p (Promotion s t k) =
      san_pawn_prefix p (Promotion u v l)" using hf by blast
  have hfile:
      "fst s = fst u"
    by (rule promotion_pawn_source_file_eq[OF hm hn hqm hqn hkm hkn
      hdest hcap hpref])
  have hsource:
      "s = u"
    by (rule promotion_pawn_source_eq[OF hm hn hqm hqn hkm hkn
      hdest hkind hfile hcap])
  show ?thesis using hsource hdest hkind by simp
qed

lemma en_passant_source_pawn:
  assumes hm: "legal_move p (EnPassant s t)"
    and hq: "position_board p s = Some q"
  shows "piece_kind q = Pawn"
proof -
  have hp: "pseudo_legal p (EnPassant s t)" using legal_move_pseudo[OF hm] .
  show ?thesis using hp hq
    by (simp add: pseudo_legal_def pseudo_legal_en_passant_def split: option.splits)
qed

lemma san_promotion_normal_conflict:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (Normal u v)"
  shows False
proof -
  have hp: "CHR ''='' \<in> set (san_non_castle_text p (Promotion s t k))"
    using san_promotion_has_equals[OF hqm] .
  have hnp: "CHR ''='' \<notin> set (san_non_castle_text p (Normal u v))"
    using san_nonpromotion_text_no_equals_normal[OF hqn] .
  have hpn: "CHR ''='' \<in> set (san_non_castle_text p (Normal u v))"
    using hp heq by simp
  show False using hnp hpn by blast
qed

lemma san_promotion_en_passant_conflict:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (EnPassant u v)"
  shows False
proof -
  have hp: "CHR ''='' \<in> set (san_non_castle_text p (Promotion s t k))"
    using san_promotion_has_equals[OF hqm] .
  have hnp: "CHR ''='' \<notin> set (san_non_castle_text p (EnPassant u v))"
    using san_nonpromotion_text_no_equals_en_passant[OF hqn] .
  have hpn: "CHR ''='' \<in> set (san_non_castle_text p (EnPassant u v))"
    using hp heq by simp
  show False using hnp hpn by blast
qed

lemma san_normal_en_passant_conflict:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (EnPassant u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (EnPassant u v)"
  shows False
proof -
  have hkn: "piece_kind qn = Pawn"
    using en_passant_source_pawn[OF hn hqn] .
  have hcapn: "move_is_capture p (EnPassant u v)"
    using en_passant_capture[OF hn] .
  show False
  proof (cases "piece_kind qm = Pawn")
    case True
    have hkm: "piece_kind qm = Pawn" using True .
    have hf:
        "t = v \<and>
         move_is_capture p (Normal s t) \<and>
         san_pawn_prefix p (Normal s t) =
           san_pawn_prefix p (EnPassant u v)"
      by (rule san_normal_en_passant_fields[OF hm hn hqm hqn True hkn heq])
    have hdest: "t = v" using hf by blast
    have hcap: "move_is_capture p (Normal s t)" using hf by blast
    have hpref:
        "san_pawn_prefix p (Normal s t) =
         san_pawn_prefix p (EnPassant u v)"
      using hf by blast
    have hcap_eq:
        "move_is_capture p (Normal s t) =
         move_is_capture p (EnPassant u v)"
      using hcap hcapn by simp
    have hfile:
        "fst s = fst u"
    proof -
      have hpre':
          "fen_file_char (fst s) = fen_file_char (fst u)"
        using hpref hqm hqn hkm hkn hcap hcapn
        by (simp add: san_pawn_prefix_def)
      show ?thesis using fen_file_char_injective hpre' by blast
    qed
    show False
      by (rule normal_en_passant_source_eq[OF hm hn hqm hqn True hkn
        hdest hcap hfile])
  next
    case False
    have hphead:
        "hd (san_non_castle_text p (Normal s t)) =
         hd (san_piece_text (piece_kind qm))"
      using san_nonpawn_head_normal[OF hqm False] .
    have hehead:
        "hd (san_non_castle_text p (EnPassant u v)) =
         fen_file_char (fst u)"
      using san_pawn_head_en_passant[OF hqn hkn hcapn] .
    have hhead:
        "hd (san_non_castle_text p (Normal s t)) =
         hd (san_non_castle_text p (EnPassant u v))"
      using heq by simp
    have hfeq:
        "hd (san_piece_text (piece_kind qm)) =
         fen_file_char (fst u)"
      using hphead hehead hhead by simp
    have hne:
        "fen_file_char (fst u) \<noteq>
         hd (san_piece_text (piece_kind qm))"
      using fen_file_char_ne_san_piece_head[OF False] .
    have hfeq':
        "fen_file_char (fst u) = hd (san_piece_text (piece_kind qm))"
      using hfeq by simp
    show False using hne hfeq' by simp
  qed
qed

lemma san_legal_noncastle_core_ne_king_castle:
  assumes hm: "legal_move p m"
    and heq: "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'']"
  shows False
proof -
  obtain q where hq: "position_board p (move_source m) = Some q"
    using legal_move_source_some[OF hm] by blast
  show False using san_noncastle_ne_castle_king[OF hq] heq by blast
qed

lemma san_legal_noncastle_core_ne_queen_castle:
  assumes hm: "legal_move p m"
    and heq: "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
  shows False
proof -
  obtain q where hq: "position_board p (move_source m) = Some q"
    using legal_move_source_some[OF hm] by blast
  show False using san_noncastle_ne_castle_queen[OF hq] heq by blast
qed

lemma san_normal_normal_injective:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and hqm: "position_board p s = Some qm"
    and hqn: "position_board p u = Some qn"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "Normal s t = Normal u v"
proof -
  consider (PP) "piece_kind qm = Pawn" "piece_kind qn = Pawn"
    | (PN) "piece_kind qm = Pawn" "piece_kind qn \<noteq> Pawn"
    | (NP) "piece_kind qm \<noteq> Pawn" "piece_kind qn = Pawn"
    | (NN) "piece_kind qm \<noteq> Pawn" "piece_kind qn \<noteq> Pawn"
    using hqm hqn
    by (cases "piece_kind qm"; cases "piece_kind qn"; simp_all)
  then show ?thesis
  proof cases
    case PP
    have hkm: "piece_kind qm = Pawn" using PP by simp
    have hkn: "piece_kind qn = Pawn" using PP by simp
    show ?thesis
      by (rule san_normal_pawn_pawn_injective[OF hm hn hqm hqn hkm hkn heq])
  next
    case PN
    have hkm: "piece_kind qm = Pawn" using PN by simp
    have hkn: "piece_kind qn \<noteq> Pawn" using PN by simp
    have hfalse: False
      by (rule san_normal_pawn_nonpawn_conflict[OF hm hn hqm hqn hkm hkn heq])
    then show ?thesis by blast
  next
    case NP
    have hkm: "piece_kind qm \<noteq> Pawn" using NP by simp
    have hkn: "piece_kind qn = Pawn" using NP by simp
    have hrev:
        "san_non_castle_text p (Normal u v) =
         san_non_castle_text p (Normal s t)"
      using heq by simp
    have hfalse: False
      by (rule san_normal_pawn_nonpawn_conflict[OF hn hm hqn hqm hkn hkm hrev])
    then show ?thesis by blast
  next
    case NN
    have hkm: "piece_kind qm \<noteq> Pawn" using NN by simp
    have hkn: "piece_kind qn \<noteq> Pawn" using NN by simp
    show ?thesis
      by (rule san_normal_nonpawn_nonpawn_injective[OF hm hn hqm hqn hkm hkn heq])
  qed
qed

lemma san_normal_normal_general:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Normal u v)"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Normal u v)"
  shows "Normal s t = Normal u v"
proof -
  obtain qm where hqm0:
      "position_board p (move_source (Normal s t)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (Normal u v)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  show ?thesis
    by (rule san_normal_normal_injective[OF hm hn hqm hqn heq])
qed

lemma castle_cross_color_conflict:
  assumes hm: "legal_move p c"
    and hc: "c = WhiteKingCastle \<or> c = WhiteQueenCastle"
    and hn: "legal_move p d"
    and hd: "d = BlackKingCastle \<or> d = BlackQueenCastle"
  shows False
proof -
  have tw: "position_turn p = White"
    by (rule castle_white_turn[OF hm hc])
  have tb: "position_turn p = Black"
    by (rule castle_black_turn[OF hn hd])
  show False using tw tb by simp
qed

lemma san_en_passant_en_passant_general:
  assumes hm: "legal_move p (EnPassant s t)"
    and hn: "legal_move p (EnPassant u v)"
    and heq: "san_non_castle_text p (EnPassant s t) =
      san_non_castle_text p (EnPassant u v)"
  shows "EnPassant s t = EnPassant u v"
proof -
  obtain qm where hqm0:
      "position_board p (move_source (EnPassant s t)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (EnPassant u v)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  have hkm: "piece_kind qm = Pawn"
    using en_passant_source_pawn[OF hm hqm] .
  have hkn: "piece_kind qn = Pawn"
    using en_passant_source_pawn[OF hn hqn] .
  have hf:
      "t = v \<and>
       san_pawn_prefix p (EnPassant s t) =
         san_pawn_prefix p (EnPassant u v)"
    by (rule san_en_passant_fields[OF hm hn hqm hqn hkm hkn heq])
  have hdest: "t = v" using hf by blast
  have hpref: "san_pawn_prefix p (EnPassant s t) =
      san_pawn_prefix p (EnPassant u v)" using hf by blast
  have hcapm: "move_is_capture p (EnPassant s t)"
    using en_passant_capture[OF hm] .
  have hcapn: "move_is_capture p (EnPassant u v)"
    using en_passant_capture[OF hn] .
  have hfile:
      "fst s = fst u"
    using hpref hqm hqn hkm hkn hcapm hcapn
    by (simp add: san_pawn_prefix_def fen_file_char_eq_iff)
  have hsource:
      "s = u"
    by (rule en_passant_source_eq[OF hm hn hqm hqn hkm hkn
      hdest hfile])
  show ?thesis using hsource hdest by simp
qed

lemma san_noncastle_castle_conflict:
  assumes hm: "legal_move p m"
    and hmc: "\<not> is_castle m"
    and hn: "legal_move p n"
    and hnc: "is_castle n"
    and heq: "san_non_castle_text p m =
      (case n of
        WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | WhiteQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | _ \<Rightarrow> [])"
  shows False
proof (cases n)
  case WhiteKingCastle
  have heq': "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq WhiteKingCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_king_castle[OF hm heq'] .
  then show ?thesis by blast
next
  case WhiteQueenCastle
  have heq': "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq WhiteQueenCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_queen_castle[OF hm heq'] .
  then show ?thesis by blast
next
  case BlackKingCastle
  have heq': "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq BlackKingCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_king_castle[OF hm heq'] .
  then show ?thesis by blast
next
  case BlackQueenCastle
  have heq': "san_non_castle_text p m =
      [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq BlackQueenCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_queen_castle[OF hm heq'] .
  then show ?thesis by blast
next
  case (Normal s t)
  then show ?thesis using hnc by simp
next
  case (Promotion s t k)
  then show ?thesis using hnc by simp
next
  case (EnPassant s t)
  then show ?thesis using hnc by simp
qed

lemma san_castle_noncastle_conflict:
  assumes hm: "legal_move p m"
    and hmc: "is_castle m"
    and hn: "legal_move p n"
    and hnc: "\<not> is_castle n"
    and heq:
      "(case m of
        WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | WhiteQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | _ \<Rightarrow> []) =
       san_non_castle_text p n"
  shows False
proof (cases m)
  case WhiteKingCastle
  have heq': "san_non_castle_text p n =
      [CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq WhiteKingCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_king_castle[OF hn heq'] .
  then show ?thesis by blast
next
  case WhiteQueenCastle
  have heq': "san_non_castle_text p n =
      [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq WhiteQueenCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_queen_castle[OF hn heq'] .
  then show ?thesis by blast
next
  case BlackKingCastle
  have heq': "san_non_castle_text p n =
      [CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq BlackKingCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_king_castle[OF hn heq'] .
  then show ?thesis by blast
next
  case BlackQueenCastle
  have heq': "san_non_castle_text p n =
      [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']"
    using heq BlackQueenCastle by simp
  have hfalse: False
    using san_legal_noncastle_core_ne_queen_castle[OF hn heq'] .
  then show ?thesis by blast
next
  case (Normal s t)
  then show ?thesis using hmc by simp
next
  case (Promotion s t k)
  then show ?thesis using hmc by simp
next
  case (EnPassant s t)
  then show ?thesis using hmc by simp
qed

lemma san_castle_pair_cases:
  assumes hmc: "is_castle m"
    and hnc: "is_castle n"
  obtains "m = WhiteKingCastle" and "n = WhiteKingCastle"
    | "m = WhiteKingCastle" and "n = WhiteQueenCastle"
    | "m = WhiteKingCastle" and "n = BlackKingCastle"
    | "m = WhiteKingCastle" and "n = BlackQueenCastle"
    | "m = WhiteQueenCastle" and "n = WhiteKingCastle"
    | "m = WhiteQueenCastle" and "n = WhiteQueenCastle"
    | "m = WhiteQueenCastle" and "n = BlackKingCastle"
    | "m = WhiteQueenCastle" and "n = BlackQueenCastle"
    | "m = BlackKingCastle" and "n = WhiteKingCastle"
    | "m = BlackKingCastle" and "n = WhiteQueenCastle"
    | "m = BlackKingCastle" and "n = BlackKingCastle"
    | "m = BlackKingCastle" and "n = BlackQueenCastle"
    | "m = BlackQueenCastle" and "n = WhiteKingCastle"
    | "m = BlackQueenCastle" and "n = WhiteQueenCastle"
    | "m = BlackQueenCastle" and "n = BlackKingCastle"
    | "m = BlackQueenCastle" and "n = BlackQueenCastle"
  using hmc hnc
  by (cases m; cases n; simp_all)

lemma castle_cross_color_conflict_fixed:
  assumes hm: "legal_move p m"
    and hn: "legal_move p n"
    and hmw: "m = WhiteKingCastle \<or> m = WhiteQueenCastle"
    and hnb: "n = BlackKingCastle \<or> n = BlackQueenCastle"
  shows False
  by (rule castle_cross_color_conflict[OF hm hmw hn hnb])

lemma san_castle_castle_injective:
  assumes hm: "legal_move p m"
    and hmc: "is_castle m"
    and hn: "legal_move p n"
    and hnc: "is_castle n"
    and heq:
      "(case m of
        WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | WhiteQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | _ \<Rightarrow> []) =
       (case n of
        WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | WhiteQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
      | BlackQueenCastle \<Rightarrow>
          [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
      | _ \<Rightarrow> [])"
  shows "m = n"
proof -
  consider (WK_WK) "m = WhiteKingCastle" "n = WhiteKingCastle"
    | (WK_WQ) "m = WhiteKingCastle" "n = WhiteQueenCastle"
    | (WK_BK) "m = WhiteKingCastle" "n = BlackKingCastle"
    | (WK_BQ) "m = WhiteKingCastle" "n = BlackQueenCastle"
    | (WQ_WK) "m = WhiteQueenCastle" "n = WhiteKingCastle"
    | (WQ_WQ) "m = WhiteQueenCastle" "n = WhiteQueenCastle"
    | (WQ_BK) "m = WhiteQueenCastle" "n = BlackKingCastle"
    | (WQ_BQ) "m = WhiteQueenCastle" "n = BlackQueenCastle"
    | (BK_WK) "m = BlackKingCastle" "n = WhiteKingCastle"
    | (BK_WQ) "m = BlackKingCastle" "n = WhiteQueenCastle"
    | (BK_BK) "m = BlackKingCastle" "n = BlackKingCastle"
    | (BK_BQ) "m = BlackKingCastle" "n = BlackQueenCastle"
    | (BQ_WK) "m = BlackQueenCastle" "n = WhiteKingCastle"
    | (BQ_WQ) "m = BlackQueenCastle" "n = WhiteQueenCastle"
    | (BQ_BK) "m = BlackQueenCastle" "n = BlackKingCastle"
    | (BQ_BQ) "m = BlackQueenCastle" "n = BlackQueenCastle"
    using hmc hnc by (rule san_castle_pair_cases)
  then show ?thesis
  proof cases
    case WK_WK then show ?thesis by simp
  next
    case WK_WQ then show ?thesis using heq by simp
  next
    case WK_BK
    have hmw: "m = WhiteKingCastle \<or> m = WhiteQueenCastle" using WK_BK by simp
    have hnb: "n = BlackKingCastle \<or> n = BlackQueenCastle" using WK_BK by simp
    have hfalse: False
      by (rule castle_cross_color_conflict_fixed[OF hm hn hmw hnb])
    then show ?thesis by blast
  next
    case WK_BQ
    have hmw: "m = WhiteKingCastle \<or> m = WhiteQueenCastle" using WK_BQ by simp
    have hnb: "n = BlackKingCastle \<or> n = BlackQueenCastle" using WK_BQ by simp
    have hfalse: False
      by (rule castle_cross_color_conflict_fixed[OF hm hn hmw hnb])
    then show ?thesis by blast
  next
    case WQ_WK then show ?thesis using heq by simp
  next
    case WQ_WQ then show ?thesis by simp
  next
    case WQ_BK
    have hmw: "m = WhiteKingCastle \<or> m = WhiteQueenCastle" using WQ_BK by simp
    have hnb: "n = BlackKingCastle \<or> n = BlackQueenCastle" using WQ_BK by simp
    have hfalse: False
      by (rule castle_cross_color_conflict_fixed[OF hm hn hmw hnb])
    then show ?thesis by blast
  next
    case WQ_BQ
    have hmw: "m = WhiteKingCastle \<or> m = WhiteQueenCastle" using WQ_BQ by simp
    have hnb: "n = BlackKingCastle \<or> n = BlackQueenCastle" using WQ_BQ by simp
    have hfalse: False
      by (rule castle_cross_color_conflict_fixed[OF hm hn hmw hnb])
    then show ?thesis by blast
  next
    case BK_WK
    have hmb: "m = BlackKingCastle \<or> m = BlackQueenCastle" using BK_WK by simp
    have hnw: "n = WhiteKingCastle \<or> n = WhiteQueenCastle" using BK_WK by simp
    have hfalse: False
      by (rule castle_cross_color_conflict[OF hn hnw hm hmb])
    then show ?thesis by blast
  next
    case BK_WQ
    have hmb: "m = BlackKingCastle \<or> m = BlackQueenCastle" using BK_WQ by simp
    have hnw: "n = WhiteKingCastle \<or> n = WhiteQueenCastle" using BK_WQ by simp
    have hfalse: False
      by (rule castle_cross_color_conflict[OF hn hnw hm hmb])
    then show ?thesis by blast
  next
    case BK_BK then show ?thesis by simp
  next
    case BK_BQ then show ?thesis using heq by simp
  next
    case BQ_WK
    have hmb: "m = BlackKingCastle \<or> m = BlackQueenCastle" using BQ_WK by simp
    have hnw: "n = WhiteKingCastle \<or> n = WhiteQueenCastle" using BQ_WK by simp
    have hfalse: False
      by (rule castle_cross_color_conflict[OF hn hnw hm hmb])
    then show ?thesis by blast
  next
    case BQ_WQ
    have hmb: "m = BlackKingCastle \<or> m = BlackQueenCastle" using BQ_WQ by simp
    have hnw: "n = WhiteKingCastle \<or> n = WhiteQueenCastle" using BQ_WQ by simp
    have hfalse: False
      by (rule castle_cross_color_conflict[OF hn hnw hm hmb])
    then show ?thesis by blast
  next
    case BQ_BK then show ?thesis using heq by simp
  next
    case BQ_BQ then show ?thesis by simp
  qed
qed

lemma san_core_case_noncastle:
  assumes hmc: "\<not> is_castle m"
  shows
    "(case m of
       WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
     | WhiteQueenCastle \<Rightarrow>
         [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
     | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
     | BlackQueenCastle \<Rightarrow>
         [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
     | _ \<Rightarrow> san_non_castle_text p m) =
     san_non_castle_text p m"
  using hmc
  by (cases m; simp_all)

lemma san_promotion_promotion_general:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Promotion u v l)"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (Promotion u v l)"
  shows "Promotion s t k = Promotion u v l"
proof -
  obtain qm where hqm0:
      "position_board p (move_source (Promotion s t k)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (Promotion u v l)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  show ?thesis
    by (rule san_promotion_promotion_injective[OF hm hn hqm hqn heq])
qed

lemma san_promotion_normal_general_conflict:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (Normal u v)"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (Normal u v)"
  shows False
proof -
  obtain qm where hqm0:
      "position_board p (move_source (Promotion s t k)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (Normal u v)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  show False
    by (rule san_promotion_normal_conflict[OF hm hn hqm hqn heq])
qed

lemma san_normal_promotion_general_conflict:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (Promotion u v k)"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (Promotion u v k)"
  shows False
proof -
  have hrev:
      "san_non_castle_text p (Promotion u v k) =
       san_non_castle_text p (Normal s t)"
    using heq by simp
  show False
    by (rule san_promotion_normal_general_conflict[OF hn hm hrev])
qed

lemma san_promotion_en_passant_general_conflict:
  assumes hm: "legal_move p (Promotion s t k)"
    and hn: "legal_move p (EnPassant u v)"
    and heq: "san_non_castle_text p (Promotion s t k) =
      san_non_castle_text p (EnPassant u v)"
  shows False
proof -
  obtain qm where hqm0:
      "position_board p (move_source (Promotion s t k)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (EnPassant u v)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  show False
    by (rule san_promotion_en_passant_conflict[OF hm hn hqm hqn heq])
qed

lemma san_en_passant_promotion_general_conflict:
  assumes hm: "legal_move p (EnPassant s t)"
    and hn: "legal_move p (Promotion u v k)"
    and heq: "san_non_castle_text p (EnPassant s t) =
      san_non_castle_text p (Promotion u v k)"
  shows False
proof -
  have hrev:
      "san_non_castle_text p (Promotion u v k) =
       san_non_castle_text p (EnPassant s t)"
    using heq by simp
  show False
    by (rule san_promotion_en_passant_general_conflict[OF hn hm hrev])
qed

lemma san_normal_en_passant_general_conflict:
  assumes hm: "legal_move p (Normal s t)"
    and hn: "legal_move p (EnPassant u v)"
    and heq: "san_non_castle_text p (Normal s t) =
      san_non_castle_text p (EnPassant u v)"
  shows False
proof -
  obtain qm where hqm0:
      "position_board p (move_source (Normal s t)) = Some qm"
    using legal_move_source_some[OF hm] by blast
  have hqm: "position_board p s = Some qm" using hqm0 by simp
  obtain qn where hqn0:
      "position_board p (move_source (EnPassant u v)) = Some qn"
    using legal_move_source_some[OF hn] by blast
  have hqn: "position_board p u = Some qn" using hqn0 by simp
  show False
    by (rule san_normal_en_passant_conflict[OF hm hn hqm hqn heq])
qed

lemma san_en_passant_normal_general_conflict:
  assumes hm: "legal_move p (EnPassant s t)"
    and hn: "legal_move p (Normal u v)"
    and heq: "san_non_castle_text p (EnPassant s t) =
      san_non_castle_text p (Normal u v)"
  shows False
proof -
  have hrev:
      "san_non_castle_text p (Normal u v) =
       san_non_castle_text p (EnPassant s t)"
    using heq by simp
  show False
    by (rule san_normal_en_passant_general_conflict[OF hn hm hrev])
qed

lemma san_noncastle_cases:
  assumes hmc: "\<not> is_castle m"
    and hnc: "\<not> is_castle n"
  obtains s t u v where "m = Normal s t" and "n = Normal u v"
    | s t u v k where "m = Normal s t" and "n = Promotion u v k"
    | s t u v where "m = Normal s t" and "n = EnPassant u v"
    | s t k u v where "m = Promotion s t k" and "n = Normal u v"
    | s t k u v l where "m = Promotion s t k" and "n = Promotion u v l"
    | s t k u v where "m = Promotion s t k" and "n = EnPassant u v"
    | s t u v where "m = EnPassant s t" and "n = Normal u v"
    | s t u v k where "m = EnPassant s t" and "n = Promotion u v k"
    | s t u v where "m = EnPassant s t" and "n = EnPassant u v"
  using hmc hnc
  by (cases m; cases n; simp_all)

lemma san_noncastle_noncastle_injective:
  assumes hm: "legal_move p m"
    and hn: "legal_move p n"
    and hmc: "\<not> is_castle m"
  and hnc: "\<not> is_castle n"
  and heq: "san_non_castle_text p m = san_non_castle_text p n"
  shows "m = n"
proof -
  consider (NN) s t u v where "m = Normal s t" and "n = Normal u v"
    | (NP) s t u v k where "m = Normal s t" and "n = Promotion u v k"
    | (NE) s t u v where "m = Normal s t" and "n = EnPassant u v"
    | (PN) s t k u v where "m = Promotion s t k" and "n = Normal u v"
    | (PP) s t k u v l where "m = Promotion s t k" and "n = Promotion u v l"
    | (PE) s t k u v where "m = Promotion s t k" and "n = EnPassant u v"
    | (EN) s t u v where "m = EnPassant s t" and "n = Normal u v"
    | (EP) s t u v k where "m = EnPassant s t" and "n = Promotion u v k"
    | (EE) s t u v where "m = EnPassant s t" and "n = EnPassant u v"
    using hmc hnc by (rule san_noncastle_cases)
  then show ?thesis
  proof cases
    case NN
    have hm': "legal_move p (Normal s t)" using hm NN by simp
    have hn': "legal_move p (Normal u v)" using hn NN by simp
    have heq': "san_non_castle_text p (Normal s t) =
        san_non_castle_text p (Normal u v)" using heq NN by simp
    have hmn: "Normal s t = Normal u v"
      using san_normal_normal_general[OF hm' hn' heq'] .
    show ?thesis using hmn NN by simp
  next
    case NP
    have hm': "legal_move p (Normal s t)" using hm NP by simp
    have hn': "legal_move p (Promotion u v k)" using hn NP by simp
    have heq': "san_non_castle_text p (Normal s t) =
        san_non_castle_text p (Promotion u v k)" using heq NP by simp
    have hfalse: False
      using san_normal_promotion_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case NE
    have hm': "legal_move p (Normal s t)" using hm NE by simp
    have hn': "legal_move p (EnPassant u v)" using hn NE by simp
    have heq': "san_non_castle_text p (Normal s t) =
        san_non_castle_text p (EnPassant u v)" using heq NE by simp
    have hfalse: False
      using san_normal_en_passant_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case PN
    have hm': "legal_move p (Promotion s t k)" using hm PN by simp
    have hn': "legal_move p (Normal u v)" using hn PN by simp
    have heq': "san_non_castle_text p (Promotion s t k) =
        san_non_castle_text p (Normal u v)" using heq PN by simp
    have hfalse: False
      using san_promotion_normal_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case PP
    have hm': "legal_move p (Promotion s t k)" using hm PP by simp
    have hn': "legal_move p (Promotion u v l)" using hn PP by simp
    have heq': "san_non_castle_text p (Promotion s t k) =
        san_non_castle_text p (Promotion u v l)" using heq PP by simp
    have hmn: "Promotion s t k = Promotion u v l"
      using san_promotion_promotion_general[OF hm' hn' heq'] .
    show ?thesis using hmn PP by simp
  next
    case PE
    have hm': "legal_move p (Promotion s t k)" using hm PE by simp
    have hn': "legal_move p (EnPassant u v)" using hn PE by simp
    have heq': "san_non_castle_text p (Promotion s t k) =
        san_non_castle_text p (EnPassant u v)" using heq PE by simp
    have hfalse: False
      using san_promotion_en_passant_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case EN
    have hm': "legal_move p (EnPassant s t)" using hm EN by simp
    have hn': "legal_move p (Normal u v)" using hn EN by simp
    have heq': "san_non_castle_text p (EnPassant s t) =
        san_non_castle_text p (Normal u v)" using heq EN by simp
    have hfalse: False
      using san_en_passant_normal_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case EP
    have hm': "legal_move p (EnPassant s t)" using hm EP by simp
    have hn': "legal_move p (Promotion u v k)" using hn EP by simp
    have heq': "san_non_castle_text p (EnPassant s t) =
        san_non_castle_text p (Promotion u v k)" using heq EP by simp
    have hfalse: False
      using san_en_passant_promotion_general_conflict[OF hm' hn' heq'] .
    then show ?thesis by blast
  next
    case EE
    have hm': "legal_move p (EnPassant s t)" using hm EE by simp
    have hn': "legal_move p (EnPassant u v)" using hn EE by simp
    have heq': "san_non_castle_text p (EnPassant s t) =
        san_non_castle_text p (EnPassant u v)" using heq EE by simp
    have hmn: "EnPassant s t = EnPassant u v"
      using san_en_passant_en_passant_general[OF hm' hn' heq'] .
    show ?thesis using hmn EE by simp
  qed
qed

lemma print_san_injective_legal_structural:
  assumes hm: "legal_move p m"
    and hn: "legal_move p n"
    and heq: "print_san p m = print_san p n"
  shows "m = n"
proof -
  have hcore:
      "san_without_check (print_san p m) =
       san_without_check (print_san p n)"
    using heq by simp
  have hcore':
      "(case m of
         WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
       | WhiteQueenCastle \<Rightarrow>
           [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
       | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
       | BlackQueenCastle \<Rightarrow>
           [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
       | _ \<Rightarrow> san_non_castle_text p m) =
       (case n of
         WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
       | WhiteQueenCastle \<Rightarrow>
           [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
       | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
       | BlackQueenCastle \<Rightarrow>
           [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
       | _ \<Rightarrow> san_non_castle_text p n)"
    using hcore san_without_check_print[of p m] san_without_check_print[of p n]
    by simp
  have hmc_cases: "is_castle m \<or> \<not> is_castle m" by blast
  have hnc_cases: "is_castle n \<or> \<not> is_castle n" by blast
  consider (CC) "is_castle m" "is_castle n"
    | (CN) "is_castle m" "\<not> is_castle n"
    | (NC) "\<not> is_castle m" "is_castle n"
    | (NN) "\<not> is_castle m" "\<not> is_castle n"
    using hmc_cases hnc_cases by blast
  then show ?thesis
  proof cases
    case CC
    have hmc: "is_castle m" using CC by simp
    have hnc: "is_castle n" using CC by simp
    have hcc:
        "(case m of
           WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | WhiteQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | _ \<Rightarrow> []) =
           (case n of
             WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
           | WhiteQueenCastle \<Rightarrow>
               [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
           | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
           | BlackQueenCastle \<Rightarrow>
               [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
           | _ \<Rightarrow> [])"
      using hcore' hmc hnc by (cases m; cases n; simp_all)
    show ?thesis
      by (rule san_castle_castle_injective[OF hm hmc hn hnc hcc])
  next
    case CN
    have hmc: "is_castle m" using CN by simp
    have hnc: "\<not> is_castle n" using CN by simp
    have hcn:
        "(case m of
           WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | WhiteQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | _ \<Rightarrow> []) = san_non_castle_text p n"
      using hcore' hmc hnc by (cases m; cases n; simp_all)
    have hfalse: False
      using san_castle_noncastle_conflict[OF hm hmc hn hnc hcn] .
    then show ?thesis by blast
  next
    case NC
    have hmc: "\<not> is_castle m" using NC by simp
    have hnc: "is_castle n" using NC by simp
    have hnc':
        "san_non_castle_text p m =
         (case n of
           WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | WhiteQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | _ \<Rightarrow> [])"
      using hcore' hmc hnc by (cases m; cases n; simp_all)
    have hfalse: False
      using san_noncastle_castle_conflict[OF hm hmc hn hnc hnc'] .
    then show ?thesis by blast
  next
    case NN
    have hmc: "\<not> is_castle m" using NN by simp
    have hnc: "\<not> is_castle n" using NN by simp
    have hmcore:
        "(case m of
           WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | WhiteQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | _ \<Rightarrow> san_non_castle_text p m) =
           san_non_castle_text p m"
      using san_core_case_noncastle[OF hmc] .
    have hncore:
        "(case n of
           WhiteKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | WhiteQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackKingCastle \<Rightarrow> [CHR ''O'', CHR ''-'', CHR ''O'']
         | BlackQueenCastle \<Rightarrow>
             [CHR ''O'', CHR ''-'', CHR ''O'', CHR ''-'', CHR ''O'']
         | _ \<Rightarrow> san_non_castle_text p n) =
           san_non_castle_text p n"
      using san_core_case_noncastle[OF hnc] .
    have hnon:
        "san_non_castle_text p m = san_non_castle_text p n"
      using hcore' hmcore hncore by simp
    show ?thesis
      by (rule san_noncastle_noncastle_injective[OF hm hn hmc hnc hnon])
  qed
qed

lemma print_san_injective_legal:
  "legal_move p m \<Longrightarrow> legal_move p n \<Longrightarrow>
   print_san p m = print_san p n \<Longrightarrow> m = n"
  using print_san_injective_legal_structural by blast

lemma parse_print_san_legal_move_unconditional:
  "legal_move p m \<Longrightarrow>
   parse_san_move p (print_san p m) = Some m"
proof -
  assume hm: "legal_move p m"
  have hu:
      "\<forall>n. legal_move p n \<and> print_san p n = print_san p m
         \<longrightarrow> n = m"
  proof (intro allI impI)
    fix n
    assume hn: "legal_move p n \<and> print_san p n = print_san p m"
    have hn': "legal_move p n" using hn by simp
    have heq0: "print_san p n = print_san p m" using hn by simp
    have heq': "print_san p m = print_san p n" using heq0 by (rule sym)
    have hmn: "m = n"
      using print_san_injective_legal[OF hm hn' heq'] .
    show "n = m" using hmn by (metis)
  qed
  show "parse_san_move p (print_san p m) = Some m"
    by (rule parse_print_san_legal_move[OF hm hu])
qed


end
