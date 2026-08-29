section \<open>Coordinate move notation\<close>

theory Chess_Notation
  imports Chess_FEN_Text Chess_Move_Generator_Correct
begin

datatype uci_move =
    UciMove square square "promotion_kind option"

fun uci_of_move :: "move \<Rightarrow> uci_move" where
  "uci_of_move (Normal s t) = UciMove s t None"
| "uci_of_move (Promotion s t k) = UciMove s t (Some k)"
| "uci_of_move (EnPassant s t) = UciMove s t None"
| "uci_of_move WhiteKingCastle = UciMove (E,R1) (G,R1) None"
| "uci_of_move WhiteQueenCastle = UciMove (E,R1) (C,R1) None"
| "uci_of_move BlackKingCastle = UciMove (E,R8) (G,R8) None"
| "uci_of_move BlackQueenCastle = UciMove (E,R8) (C,R8) None"

definition uci_witness :: "position \<Rightarrow> uci_move \<Rightarrow> bool" where
  "uci_witness p u \<longleftrightarrow>
    (\<exists>m. legal_move p m \<and> uci_of_move m = u)"

definition parse_uci_move :: "position \<Rightarrow> uci_move \<Rightarrow> move option" where
  "parse_uci_move p u =
    List.find (\<lambda>m. legal_move p m \<and> uci_of_move m = u)
      (legal_moves p)"

definition print_uci_move :: "position \<Rightarrow> move \<Rightarrow> uci_move" where
  "print_uci_move p m = uci_of_move m"

lemma normal_en_passant_pseudo_conflict:
  "normal_pseudo_legal p s t \<Longrightarrow>
   pseudo_legal_en_passant p (EnPassant s t) \<Longrightarrow> False"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def pseudo_legal_en_passant_def
      pawn_move_geometry_def pawn_attack_geometry_def
      pawn_double_geometry_def split: option.splits if_splits)

lemma normal_white_king_castle_pseudo_conflict:
  "normal_pseudo_legal p (E,R1) (G,R1) \<Longrightarrow>
   pseudo_legal_castle p WhiteKingCastle \<Longrightarrow> False"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def king_geometry_def pseudo_legal_castle_def
      castle_empty_squares_def has_piece_def file_index_def rank_index_def
      split: option.splits if_splits)

lemma normal_white_queen_castle_pseudo_conflict:
  "normal_pseudo_legal p (E,R1) (C,R1) \<Longrightarrow>
   pseudo_legal_castle p WhiteQueenCastle \<Longrightarrow> False"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def king_geometry_def pseudo_legal_castle_def
      castle_empty_squares_def has_piece_def file_index_def rank_index_def
      split: option.splits if_splits)

lemma normal_black_king_castle_pseudo_conflict:
  "normal_pseudo_legal p (E,R8) (G,R8) \<Longrightarrow>
   pseudo_legal_castle p BlackKingCastle \<Longrightarrow> False"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def king_geometry_def pseudo_legal_castle_def
      castle_empty_squares_def has_piece_def file_index_def rank_index_def
      split: option.splits if_splits)

lemma normal_black_queen_castle_pseudo_conflict:
  "normal_pseudo_legal p (E,R8) (C,R8) \<Longrightarrow>
   pseudo_legal_castle p BlackQueenCastle \<Longrightarrow> False"
  by (auto simp add: normal_pseudo_legal_def destination_friendly_def
      normal_piece_geometry_def king_geometry_def pseudo_legal_castle_def
      castle_empty_squares_def has_piece_def file_index_def rank_index_def
      split: option.splits if_splits)

lemma en_passant_castle_pseudo_conflict:
  "pseudo_legal_en_passant p (EnPassant s t) \<Longrightarrow>
   pseudo_legal_castle p c \<Longrightarrow>
   (s,t) \<noteq> ((E,R1),(G,R1)) \<and>
   (s,t) \<noteq> ((E,R1),(C,R1)) \<and>
   (s,t) \<noteq> ((E,R8),(G,R8)) \<and>
   (s,t) \<noteq> ((E,R8),(C,R8))"
  by (cases c; auto simp add: pseudo_legal_en_passant_def
      pseudo_legal_castle_def ep_captured_square_def
      pawn_attack_geometry_def has_piece_def split: option.splits if_splits)

lemma uci_of_move_legal_injective:
  assumes hm: "legal_move p m" and hn: "legal_move p n"
    and hu: "uci_of_move m = uci_of_move n"
  shows "m = n"
proof -
  have hmp: "pseudo_legal p m" using legal_move_pseudo[OF hm] .
  have hnp: "pseudo_legal p n" using legal_move_pseudo[OF hn] .
  show ?thesis
    using hm hn hu hmp hnp
    by (cases m; cases n;
        simp_all add: uci_of_move.simps legal_move_pseudo pseudo_legal_def
          normal_en_passant_pseudo_conflict
          normal_white_king_castle_pseudo_conflict
          normal_white_queen_castle_pseudo_conflict
          normal_black_king_castle_pseudo_conflict
          normal_black_queen_castle_pseudo_conflict
          en_passant_castle_pseudo_conflict;
        metis normal_en_passant_pseudo_conflict
          normal_white_king_castle_pseudo_conflict
          normal_white_queen_castle_pseudo_conflict
          normal_black_king_castle_pseudo_conflict
          normal_black_queen_castle_pseudo_conflict
          en_passant_castle_pseudo_conflict)
qed

lemma uci_of_move_legal_injective_rev:
  assumes hn: "legal_move p n" and hm: "legal_move p m"
    and hu: "uci_of_move n = uci_of_move m"
  shows "n = m"
  using uci_of_move_legal_injective[OF hn hm] hu
  by (metis)

lemma uci_unique_on_legal_move:
  "legal_move p m \<Longrightarrow>
   (\<forall>n. legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m)"
  using uci_of_move_legal_injective_rev
  by (auto intro: uci_of_move_legal_injective_rev)

lemma uci_list_find_unique:
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

lemma parse_print_uci_legal_move:
  "legal_move p m \<Longrightarrow>
   (\<forall>n. legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m) \<Longrightarrow>
   parse_uci_move p (print_uci_move p m) = Some m"
proof -
  assume hm: "legal_move p m"
  have hu:
    "\<forall>n. legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m"
    using hm by (auto intro: uci_of_move_legal_injective_rev)
  have hm_mem: "m \<in> set (legal_moves p)"
    using legal_moves_complete hm by simp
  have hfind:
      "List.find
        (\<lambda>n. legal_move p n \<and> uci_of_move n = uci_of_move m)
        (legal_moves p) = Some m"
  proof (rule uci_list_find_unique[OF hm_mem])
    show "legal_move p m \<and> uci_of_move m = uci_of_move m"
      by (simp add: hm)
  next
    show "\<forall>n \<in> set (legal_moves p).
        legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m"
      using hu by blast
  qed
  show ?thesis
    by (simp add: parse_uci_move_def print_uci_move_def hfind)
qed

lemma parse_print_uci_legal_move_unique:
  "legal_move p m \<Longrightarrow>
   parse_uci_move p (print_uci_move p m) = Some m"
proof -
  assume hm: "legal_move p m"
  have hu:
      "\<forall>n. legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m"
    using uci_unique_on_legal_move[OF hm] .
  show ?thesis
    by (rule parse_print_uci_legal_move[OF hm hu])
qed

text \<open>
  The datatype-level UCI layer above is complemented by a canonical textual
  wire representation.  Castling is encoded by its king coordinate pair, so
  the position-dependent parser resolves it through the legal move relation.
\<close>

definition uci_text_square :: "square \<Rightarrow> string" where
  "uci_text_square s =
    [fen_file_char (fst s), fen_rank_char (snd s)]"

fun uci_text_promotion_char :: "promotion_kind \<Rightarrow> char" where
  "uci_text_promotion_char PromoteQueen = CHR ''q''"
| "uci_text_promotion_char PromoteRook = CHR ''r''"
| "uci_text_promotion_char PromoteBishop = CHR ''b''"
| "uci_text_promotion_char PromoteKnight = CHR ''n''"

fun promotion_kind_of_uci_text_char :: "char \<Rightarrow> promotion_kind option" where
  "promotion_kind_of_uci_text_char (CHR ''q'') = Some PromoteQueen"
| "promotion_kind_of_uci_text_char (CHR ''r'') = Some PromoteRook"
| "promotion_kind_of_uci_text_char (CHR ''b'') = Some PromoteBishop"
| "promotion_kind_of_uci_text_char (CHR ''n'') = Some PromoteKnight"
| "promotion_kind_of_uci_text_char _ = None"

definition uci_text_of_uci :: "uci_move \<Rightarrow> string" where
  "uci_text_of_uci u =
    (case u of
       UciMove s t None \<Rightarrow> uci_text_square s @ uci_text_square t
     | UciMove s t (Some k) \<Rightarrow>
         uci_text_square s @ uci_text_square t @
           [uci_text_promotion_char k])"

fun parse_uci_text_raw :: "string \<Rightarrow> uci_move option" where
  "parse_uci_text_raw [sf, sr, tf, tr] =
     (case (fen_file_of_char sf, fen_rank_of_char sr,
            fen_file_of_char tf, fen_rank_of_char tr) of
        (Some f, Some r, Some f', Some r') \<Rightarrow>
          Some (UciMove (f,r) (f',r') None)
      | _ \<Rightarrow> None)"
| "parse_uci_text_raw [sf, sr, tf, tr, pk] =
     (case (fen_file_of_char sf, fen_rank_of_char sr,
            fen_file_of_char tf, fen_rank_of_char tr,
            promotion_kind_of_uci_text_char pk) of
        (Some f, Some r, Some f', Some r', Some k) \<Rightarrow>
          Some (UciMove (f,r) (f',r') (Some k))
      | _ \<Rightarrow> None)"
| "parse_uci_text_raw _ = None"

definition parse_uci_text :: "position \<Rightarrow> string \<Rightarrow> move option" where
  "parse_uci_text p s =
    (case parse_uci_text_raw s of
       None \<Rightarrow> None
     | Some u \<Rightarrow> parse_uci_move p u)"

definition print_uci_text :: "position \<Rightarrow> move \<Rightarrow> string" where
  "print_uci_text p m = uci_text_of_uci (print_uci_move p m)"

lemma uci_text_square_parse:
  "parse_uci_text_raw
      (uci_text_square s @ uci_text_square t) =
    Some (UciMove s t None)"
proof (cases s; cases t;
    simp add: uci_text_square_def fen_file_of_char_file_char
      fen_rank_of_char_rank_char)
qed

lemma uci_text_square_parse_promotion:
  "parse_uci_text_raw
      (uci_text_square s @ uci_text_square t @
        [uci_text_promotion_char k]) =
    Some (UciMove s t (Some k))"
proof (cases s; cases t; cases k;
    simp add: uci_text_square_def uci_text_promotion_char.simps
      fen_file_of_char_file_char fen_rank_of_char_rank_char
      promotion_kind_of_uci_text_char.simps)
qed

lemma parse_uci_text_raw_uci_text:
  "parse_uci_text_raw (uci_text_of_uci u) = Some u"
  by (cases u; simp split: option.splits
      add: uci_text_of_uci_def uci_text_square_parse
        uci_text_square_parse_promotion)

lemma parse_print_uci_text_legal_move:
  "legal_move p m \<Longrightarrow>
   parse_uci_text p (print_uci_text p m) = Some m"
proof -
  assume hm: "legal_move p m"
  have hu:
    "\<forall>n. legal_move p n \<and> uci_of_move n = uci_of_move m \<longrightarrow> n = m"
    using hm by (auto intro: uci_of_move_legal_injective_rev)
  have hraw:
      "parse_uci_text_raw (uci_text_of_uci (uci_of_move m)) =
        Some (uci_of_move m)"
    by (rule parse_uci_text_raw_uci_text)
  have hparse:
      "parse_uci_move p (uci_of_move m) = Some m"
    using parse_print_uci_legal_move[OF hm hu]
    by (simp add: print_uci_move_def)
  show ?thesis
    using hraw hparse
    by (simp add: parse_uci_text_def print_uci_text_def
      print_uci_move_def)
qed

end
