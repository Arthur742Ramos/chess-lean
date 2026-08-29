section \<open>Chess positions and invariants\<close>

theory Chess_Position
  imports Chess_Board
begin

datatype castle_right = WhiteKingSide | WhiteQueenSide | BlackKingSide | BlackQueenSide

type_synonym castling_rights = "castle_right set"

record position =
  position_board :: board
  position_turn :: color
  position_castling :: castling_rights
  position_en_passant :: "square option"
  position_halfmove :: nat
  position_fullmove :: nat

definition king_squares :: "board \<Rightarrow> color \<Rightarrow> square set" where
  "king_squares b c = squares_of b c King"

definition has_piece :: "board \<Rightarrow> square \<Rightarrow> color \<Rightarrow> piece_kind \<Rightarrow> bool" where
  "has_piece b s c k \<longleftrightarrow>
     (case b s of
        Some p \<Rightarrow> piece_color p = c \<and> piece_kind p = k
      | None \<Rightarrow> False)"

definition exactly_one_king :: "board \<Rightarrow> color \<Rightarrow> bool" where
  "exactly_one_king b c \<longleftrightarrow>
     length (filter (\<lambda>s. has_piece b s c King) all_squares) = 1"

definition pawn_on_promotion_rank :: "board \<Rightarrow> bool" where
  "pawn_on_promotion_rank b \<longleftrightarrow>
     filter (\<lambda>s. case b s of
       Some p \<Rightarrow> piece_kind p = Pawn \<and>
         (snd s = R1 \<or> snd s = R8)
     | None \<Rightarrow> False) all_squares \<noteq> []"

definition rights_consistent :: "position \<Rightarrow> bool" where
  "rights_consistent p \<longleftrightarrow>
     (WhiteKingSide \<in> position_castling p \<longrightarrow>
       has_piece (position_board p) (E, R1) White King \<and>
       has_piece (position_board p) (H, R1) White Rook) \<and>
     (WhiteQueenSide \<in> position_castling p \<longrightarrow>
       has_piece (position_board p) (E, R1) White King \<and>
       has_piece (position_board p) (A, R1) White Rook) \<and>
     (BlackKingSide \<in> position_castling p \<longrightarrow>
       has_piece (position_board p) (E, R8) Black King \<and>
       has_piece (position_board p) (H, R8) Black Rook) \<and>
     (BlackQueenSide \<in> position_castling p \<longrightarrow>
       has_piece (position_board p) (E, R8) Black King \<and>
       has_piece (position_board p) (A, R8) Black Rook)"

fun right_color :: "castle_right \<Rightarrow> color" where
  "right_color WhiteKingSide = White"
| "right_color WhiteQueenSide = White"
| "right_color BlackKingSide = Black"
| "right_color BlackQueenSide = Black"

fun right_king_square :: "castle_right \<Rightarrow> square" where
  "right_king_square WhiteKingSide = (E,R1)"
| "right_king_square WhiteQueenSide = (E,R1)"
| "right_king_square BlackKingSide = (E,R8)"
| "right_king_square BlackQueenSide = (E,R8)"

fun right_rook_square :: "castle_right \<Rightarrow> square" where
  "right_rook_square WhiteKingSide = (H,R1)"
| "right_rook_square WhiteQueenSide = (A,R1)"
| "right_rook_square BlackKingSide = (H,R8)"
| "right_rook_square BlackQueenSide = (A,R8)"

lemma rights_consistent_iff:
  "rights_consistent p \<longleftrightarrow>
    (\<forall>r \<in> position_castling p.
       has_piece (position_board p) (right_king_square r) (right_color r) King \<and>
       has_piece (position_board p) (right_rook_square r) (right_color r) Rook)"
proof (rule iffI)
  assume h: "rights_consistent p"
  show "\<forall>r \<in> position_castling p.
      has_piece (position_board p) (right_king_square r) (right_color r) King \<and>
      has_piece (position_board p) (right_rook_square r) (right_color r) Rook"
  proof
    fix r
    assume hr: "r \<in> position_castling p"
    show "has_piece (position_board p) (right_king_square r) (right_color r) King \<and>
      has_piece (position_board p) (right_rook_square r) (right_color r) Rook"
      using h hr by (cases r; simp add: rights_consistent_def)
  qed
next
  assume h:
    "\<forall>r \<in> position_castling p.
      has_piece (position_board p) (right_king_square r) (right_color r) King \<and>
      has_piece (position_board p) (right_rook_square r) (right_color r) Rook"
  show "rights_consistent p"
    using h by (auto simp add: rights_consistent_def split: castle_right.splits)
qed

definition position_invariant :: "position \<Rightarrow> bool" where
  "position_invariant p \<longleftrightarrow>
     exactly_one_king (position_board p) White \<and>
     exactly_one_king (position_board p) Black \<and>
     \<not> pawn_on_promotion_rank (position_board p) \<and>
     rights_consistent p \<and>
     position_fullmove p > 0"

fun initial_piece :: "square \<Rightarrow> piece option" where
  "initial_piece (A, R1) = Some \<lparr>piece_color = White, piece_kind = Rook\<rparr>"
| "initial_piece (B, R1) = Some \<lparr>piece_color = White, piece_kind = Knight\<rparr>"
| "initial_piece (C, R1) = Some \<lparr>piece_color = White, piece_kind = Bishop\<rparr>"
| "initial_piece (D, R1) = Some \<lparr>piece_color = White, piece_kind = Queen\<rparr>"
| "initial_piece (E, R1) = Some \<lparr>piece_color = White, piece_kind = King\<rparr>"
| "initial_piece (F, R1) = Some \<lparr>piece_color = White, piece_kind = Bishop\<rparr>"
| "initial_piece (G, R1) = Some \<lparr>piece_color = White, piece_kind = Knight\<rparr>"
| "initial_piece (H, R1) = Some \<lparr>piece_color = White, piece_kind = Rook\<rparr>"
| "initial_piece (A, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (B, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (C, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (D, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (E, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (F, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (G, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (H, R2) = Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>"
| "initial_piece (A, R8) = Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>"
| "initial_piece (B, R8) = Some \<lparr>piece_color = Black, piece_kind = Knight\<rparr>"
| "initial_piece (C, R8) = Some \<lparr>piece_color = Black, piece_kind = Bishop\<rparr>"
| "initial_piece (D, R8) = Some \<lparr>piece_color = Black, piece_kind = Queen\<rparr>"
| "initial_piece (E, R8) = Some \<lparr>piece_color = Black, piece_kind = King\<rparr>"
| "initial_piece (F, R8) = Some \<lparr>piece_color = Black, piece_kind = Bishop\<rparr>"
| "initial_piece (G, R8) = Some \<lparr>piece_color = Black, piece_kind = Knight\<rparr>"
| "initial_piece (H, R8) = Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>"
| "initial_piece (A, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (B, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (C, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (D, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (E, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (F, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (G, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece (H, R7) = Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>"
| "initial_piece _ = None"

definition initial_position :: position where
  "initial_position =
    \<lparr>position_board = initial_piece,
     position_turn = White,
     position_castling = {WhiteKingSide, WhiteQueenSide, BlackKingSide, BlackQueenSide},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma initial_piece_king:
  "initial_piece (E, R1) = Some \<lparr>piece_color = White, piece_kind = King\<rparr>"
  "initial_piece (E, R8) = Some \<lparr>piece_color = Black, piece_kind = King\<rparr>"
  by simp_all

lemma initial_position_fullmove: "position_fullmove initial_position = 1"
  by (simp add: initial_position_def)

lemma initial_position_kings:
  "exactly_one_king (position_board initial_position) White \<and>
   exactly_one_king (position_board initial_position) Black"
  by (simp add: initial_position_def exactly_one_king_def has_piece_def
      all_squares_def all_files_def all_ranks_def)

lemma initial_position_no_pawn_on_promotion_rank:
  "\<not> pawn_on_promotion_rank (position_board initial_position)"
  by (simp add: initial_position_def pawn_on_promotion_rank_def
      all_squares_def all_files_def all_ranks_def)

lemma initial_position_rights_consistent:
  "rights_consistent initial_position"
  by (simp add: initial_position_def rights_consistent_def has_piece_def)

lemma position_invariant_iff:
  "position_invariant p \<longleftrightarrow>
     exactly_one_king (position_board p) White \<and>
     exactly_one_king (position_board p) Black \<and>
     \<not> pawn_on_promotion_rank (position_board p) \<and>
     rights_consistent p \<and>
     position_fullmove p > 0"
  by (simp add: position_invariant_def)

lemma filter_nonempty_iff:
  "filter P xs \<noteq> [] \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  by (induct xs) simp_all

lemma pawn_on_promotion_rank_iff:
  "pawn_on_promotion_rank b \<longleftrightarrow>
   (\<exists>s \<in> set all_squares.
      (case b s of
         Some p \<Rightarrow> piece_kind p = Pawn \<and>
           (snd s = R1 \<or> snd s = R8)
       | None \<Rightarrow> False))"
  by (simp add: pawn_on_promotion_rank_def filter_nonempty_iff)

lemma exactly_one_king_card:
  "exactly_one_king b c \<longleftrightarrow> card (king_squares b c) = 1"
proof -
  have hset:
      "{s. has_piece b s c King} = squares_of b c King"
    by (auto simp add: has_piece_def squares_of_def split: option.splits)
  show ?thesis
    by (simp add: exactly_one_king_def king_squares_def
        distinct_length_filter all_squares_distinct all_squares_set hset)
qed

lemma squares_of_board_move:
  "s \<noteq> t \<Longrightarrow>
   squares_of (board_move b s t) c k =
     (squares_of b c k - {s, t}) \<union>
       (if has_piece b s c k then {t} else {})"
proof -
  assume st: "s \<noteq> t"
  show "squares_of (board_move b s t) c k =
      (squares_of b c k - {s, t}) \<union>
        (if has_piece b s c k then {t} else {})"
  proof (rule set_eqI)
    fix u
    show "u \<in> squares_of (board_move b s t) c k \<longleftrightarrow>
        u \<in> (squares_of b c k - {s, t}) \<union>
          (if has_piece b s c k then {t} else {})"
      by (cases "u = s"; cases "u = t"; cases "has_piece b s c k";
          auto simp add: squares_of_def board_move_def board_update_def
            has_piece_def st split: option.splits)
  qed
qed

lemma has_piece_iff_squares_of:
  "has_piece b s c k \<longleftrightarrow> s \<in> squares_of b c k"
  by (auto simp add: has_piece_def squares_of_def split: option.splits)

lemma move_card_piece:
  assumes st: "s \<noteq> t"
    and ht: "t \<notin> squares_of b c k"
    and hs: "has_piece b s c k"
  shows "card (squares_of (board_move b s t) c k) = card (squares_of b c k)"
proof -
  have fin: "finite (squares_of b c k)"
  proof (rule finite_subset[of "squares_of b c k" "set all_squares"])
    show "squares_of b c k \<subseteq> set all_squares"
      by (simp add: all_squares_set)
    show "finite (set all_squares)" by simp
  qed
  have hsmem: "s \<in> squares_of b c k"
    using has_piece_iff_squares_of hs by blast
  have hcard1:
      "card (squares_of b c k - {s, t}) =
        card (squares_of b c k - {t}) - 1"
    using card_Diff_insert[OF hsmem] by (simp add: st)
  have hcard2: "card (squares_of b c k - {t}) = card (squares_of b c k)"
    by (simp add: ht fin)
  have hcard: "card (squares_of b c k - {s, t}) = card (squares_of b c k) - 1"
    using hcard1 hcard2 by simp
  have hpos: "0 < card (squares_of b c k)"
  proof -
    have hne: "squares_of b c k \<noteq> {}" using hsmem by blast
    show ?thesis by (simp add: card_gt_0_iff hne fin)
  qed
  show ?thesis
    by (simp add: squares_of_board_move[OF st] hs ht hsmem hcard fin
        card_insert_if card_Diff_singleton hpos)
qed

lemma move_card_empty:
  assumes st: "s \<noteq> t"
    and ht: "t \<notin> squares_of b c k"
    and hs: "\<not> has_piece b s c k"
  shows "card (squares_of (board_move b s t) c k) = card (squares_of b c k)"
proof -
  have fin: "finite (squares_of b c k)"
  proof (rule finite_subset[of "squares_of b c k" "set all_squares"])
    show "squares_of b c k \<subseteq> set all_squares"
      by (simp add: all_squares_set)
    show "finite (set all_squares)" by simp
  qed
  have hsmem: "s \<notin> squares_of b c k"
    using has_piece_iff_squares_of hs by blast
  show ?thesis
    by (simp add: squares_of_board_move[OF st] hs ht hsmem fin
        card_insert_if card_Diff_singleton)
qed

lemma exactly_one_king_board_move:
  assumes st: "s \<noteq> t"
    and hk: "exactly_one_king b c"
    and ht: "\<not> has_piece b t c King"
  shows "exactly_one_king (board_move b s t) c"
proof -
  have hcard: "card (squares_of b c King) = 1"
    using exactly_one_king_card hk by (simp add: king_squares_def)
  have hcases: "has_piece b s c King \<or> \<not> has_piece b s c King"
    by blast
  show ?thesis
  proof (rule disjE[OF hcases])
    assume hs: "has_piece b s c King"
    have htm: "t \<notin> squares_of b c King"
      using has_piece_iff_squares_of ht by blast
    have hmcard:
        "card (squares_of (board_move b s t) c King) =
          card (squares_of b c King)"
      using st htm hs by (rule move_card_piece)
    have hnew: "card (squares_of (board_move b s t) c King) = 1"
      using hmcard hcard by simp
    show ?thesis
      using exactly_one_king_card[of "board_move b s t" c] hnew
      by (simp add: king_squares_def)
  next
    assume hs: "\<not> has_piece b s c King"
    have htm: "t \<notin> squares_of b c King"
      using has_piece_iff_squares_of ht by blast
    have hmcard:
        "card (squares_of (board_move b s t) c King) =
          card (squares_of b c King)"
      using st htm hs by (rule move_card_empty)
    have hnew: "card (squares_of (board_move b s t) c King) = 1"
      using hmcard hcard by simp
    show ?thesis
      using exactly_one_king_card[of "board_move b s t" c] hnew
      by (simp add: king_squares_def)
  qed
qed

lemma squares_of_board_update_unchanged:
  assumes old: "\<not> has_piece b s c k"
    and new: "\<not> has_piece (board_update b s x) s c k"
  shows "squares_of (board_update b s x) c k = squares_of b c k"
proof (rule set_eqI)
  fix u
  have old':
      "\<not> (\<exists>p. b s = Some p \<and>
        piece_color p = c \<and> piece_kind p = k)"
    using old by (simp add: has_piece_def split: option.splits)
  have new':
      "\<not> (\<exists>p. x = Some p \<and>
        piece_color p = c \<and> piece_kind p = k)"
    using new by (simp add: has_piece_def board_update_def split: option.splits)
  show "u \<in> squares_of (board_update b s x) c k \<longleftrightarrow>
      u \<in> squares_of b c k"
  proof (cases "u = s")
    case True
      show ?thesis using old' new'
        by (simp add: squares_of_def board_update_def True
          split: option.splits; blast)
  next
    case False
      show ?thesis by (simp add: squares_of_def board_update_def False)
  qed
qed

lemma exactly_one_king_board_update_unchanged:
  assumes hk: "exactly_one_king b c"
    and old: "\<not> has_piece b s c King"
    and new: "\<not> has_piece (board_update b s x) s c King"
  shows "exactly_one_king (board_update b s x) c"
proof -
  have hcard: "card (squares_of b c King) = 1"
    using exactly_one_king_card hk by (simp add: king_squares_def)
  have hset: "squares_of (board_update b s x) c King = squares_of b c King"
    by (rule squares_of_board_update_unchanged[OF old new])
  have hnew: "card (squares_of (board_update b s x) c King) = 1"
    using hset hcard by simp
  show ?thesis
    using exactly_one_king_card[of "board_update b s x" c] hnew
    by (simp add: king_squares_def)
qed

lemma exactly_one_king_two_updates:
  assumes hk: "exactly_one_king b c"
    and old1: "\<not> has_piece b s c King"
    and new1: "\<not> has_piece (board_update b s x) s c King"
    and old2: "\<not> has_piece (board_update b s x) t c King"
    and new2: "\<not> has_piece (board_update (board_update b s x) t y) t c King"
  shows "exactly_one_king (board_update (board_update b s x) t y) c"
proof -
  have h1: "exactly_one_king (board_update b s x) c"
    by (rule exactly_one_king_board_update_unchanged[OF hk old1 new1])
  show ?thesis
    by (rule exactly_one_king_board_update_unchanged[OF h1 old2 new2])
qed

end
