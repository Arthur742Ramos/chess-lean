theory Chess_FEN_Text
  imports Chess_FEN
begin

type_synonym fen_string = string

definition fen_ranks :: "rank list" where
  "fen_ranks = [R8, R7, R6, R5, R4, R3, R2, R1]"

definition fen_file_char :: "chess_file => char" where
  "fen_file_char f =
    (case f of A => CHR ''a'' | B => CHR ''b'' | C => CHR ''c'' |
       D => CHR ''d'' | E => CHR ''e'' | F => CHR ''f'' |
       G => CHR ''g'' | H => CHR ''h'')"

definition fen_rank_char :: "rank => char" where
  "fen_rank_char r =
    (case r of R1 => CHR ''1'' | R2 => CHR ''2'' | R3 => CHR ''3'' |
       R4 => CHR ''4'' | R5 => CHR ''5'' | R6 => CHR ''6'' |
       R7 => CHR ''7'' | R8 => CHR ''8'')"

definition fen_file_of_char :: "char => chess_file option" where
  "fen_file_of_char c =
    (if c = CHR ''a'' then Some A else if c = CHR ''b'' then Some B else
     if c = CHR ''c'' then Some C else if c = CHR ''d'' then Some D else
     if c = CHR ''e'' then Some E else if c = CHR ''f'' then Some F else
     if c = CHR ''g'' then Some G else if c = CHR ''h'' then Some H else None)"

definition fen_rank_of_char :: "char => rank option" where
  "fen_rank_of_char c =
    (if c = CHR ''1'' then Some R1 else if c = CHR ''2'' then Some R2 else
     if c = CHR ''3'' then Some R3 else if c = CHR ''4'' then Some R4 else
     if c = CHR ''5'' then Some R5 else if c = CHR ''6'' then Some R6 else
     if c = CHR ''7'' then Some R7 else if c = CHR ''8'' then Some R8 else None)"

definition fen_piece_char_of :: "color => piece_kind => char" where
  "fen_piece_char_of c k =
    (case c of
       White => (case k of King => CHR ''K'' | Queen => CHR ''Q'' |
         Rook => CHR ''R'' | Bishop => CHR ''B'' |
         Knight => CHR ''N'' | Pawn => CHR ''P'')
     | Black => (case k of King => CHR ''k'' | Queen => CHR ''q'' |
         Rook => CHR ''r'' | Bishop => CHR ''b'' |
         Knight => CHR ''n'' | Pawn => CHR ''p''))"

definition fen_piece_char :: "piece => char" where
  "fen_piece_char p = fen_piece_char_of (piece_color p) (piece_kind p)"

definition fen_piece_of_char :: "char => piece option" where
  "fen_piece_of_char c =
    (if c = CHR ''K'' then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
     else if c = CHR ''Q'' then Some \<lparr>piece_color = White, piece_kind = Queen\<rparr>
     else if c = CHR ''R'' then Some \<lparr>piece_color = White, piece_kind = Rook\<rparr>
     else if c = CHR ''B'' then Some \<lparr>piece_color = White, piece_kind = Bishop\<rparr>
     else if c = CHR ''N'' then Some \<lparr>piece_color = White, piece_kind = Knight\<rparr>
     else if c = CHR ''P'' then Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>
     else if c = CHR ''k'' then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
     else if c = CHR ''q'' then Some \<lparr>piece_color = Black, piece_kind = Queen\<rparr>
     else if c = CHR ''r'' then Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>
     else if c = CHR ''b'' then Some \<lparr>piece_color = Black, piece_kind = Bishop\<rparr>
     else if c = CHR ''n'' then Some \<lparr>piece_color = Black, piece_kind = Knight\<rparr>
     else if c = CHR ''p'' then Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>
     else None)"

lemma fen_file_of_char_file_char:
  "fen_file_of_char (fen_file_char f) = Some f"
  by (cases f; simp add: fen_file_of_char_def fen_file_char_def)

lemma fen_rank_of_char_rank_char:
  "fen_rank_of_char (fen_rank_char r) = Some r"
  by (cases r; simp add: fen_rank_of_char_def fen_rank_char_def)

lemma fen_piece_of_char_piece_char:
  "fen_piece_of_char (fen_piece_char p) = Some p"
proof -
  obtain c k where hp: "p = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases p; simp)
  show ?thesis
    using hp by (cases c; cases k;
      simp add: fen_piece_of_char_def fen_piece_char_def fen_piece_char_of_def)
qed

definition fen_digit_value :: "char => nat option" where
  "fen_digit_value c =
    (if c = CHR ''1'' then Some 1 else if c = CHR ''2'' then Some 2 else
     if c = CHR ''3'' then Some 3 else if c = CHR ''4'' then Some 4 else
     if c = CHR ''5'' then Some 5 else if c = CHR ''6'' then Some 6 else
     if c = CHR ''7'' then Some 7 else if c = CHR ''8'' then Some 8 else None)"

definition fen_digit_char :: "nat => char" where
  "fen_digit_char n =
    (if n = 0 then CHR ''0'' else if n = 1 then CHR ''1'' else
     if n = 2 then CHR ''2'' else if n = 3 then CHR ''3'' else
     if n = 4 then CHR ''4'' else if n = 5 then CHR ''5'' else
     if n = 6 then CHR ''6'' else if n = 7 then CHR ''7'' else
     if n = 8 then CHR ''8'' else if n = 9 then CHR ''9'' else CHR ''0'')"

function fen_nat_digits :: "nat => string" where
  "fen_nat_digits n =
     (if n = 0 then [CHR ''0'']
      else if n < 10 then [fen_digit_char n]
      else fen_nat_digits (n div 10) @ [fen_digit_char (n mod 10)])"
  by pat_completeness auto
termination
  by (relation "measure id") (auto simp: div_less_iff_less_mult)

fun fen_chunk :: "char => piece option list option" where
  "fen_chunk c =
    (case fen_piece_of_char c of
       Some p => Some [Some p]
     | None =>
         (case fen_digit_value c of
            Some n => Some (replicate n None)
          | None => None))"

fun parse_fen_rank_cells :: "string => piece option list option" where
  "parse_fen_rank_cells [] = Some []"
| "parse_fen_rank_cells (c#cs) =
    (case fen_chunk c of
       None => None
     | Some xs =>
         (case parse_fen_rank_cells cs of
            None => None
          | Some ys => Some (xs @ ys)))"

lemma parse_fen_rank_cells_append:
  "parse_fen_rank_cells (xs @ ys) =
    (case parse_fen_rank_cells xs of
       None => None
     | Some zs =>
         (case parse_fen_rank_cells ys of
            None => None | Some ws => Some (zs @ ws)))"
  by (induct xs) (simp_all split: option.splits)

lemma fen_chunk_digit:
  assumes hpos: "0 < n" and hle: "n \<le> 8"
  shows "fen_chunk (fen_digit_char n) = Some (replicate n None)"
proof -
  have hn: "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or>
      n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8"
    using hpos hle by arith
  then show ?thesis
    using hpos by (elim disjE; simp add: fen_chunk.simps fen_digit_value_def
      fen_digit_char_def fen_piece_of_char_def)
qed

lemma fen_piece_of_char_digit_char:
  assumes hpos: "0 < n" and hle: "n \<le> 8"
  shows "fen_piece_of_char (fen_digit_char n) = None"
proof -
  have hn: "n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or>
      n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8"
    using hpos hle by arith
  then show ?thesis
    by (elim disjE; simp add: fen_digit_char_def fen_piece_of_char_def)
qed

lemma fen_digit_value_digit_char:
  assumes hpos: "0 < n" and hle: "n \<le> 8"
  shows "fen_digit_value (fen_digit_char n) = Some n"
proof -
  have hn: "n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or>
      n = 5 \<or> n = 6 \<or> n = 7 \<or> n = 8"
    using hpos hle by arith
  then show ?thesis
    by (elim disjE; simp add: fen_digit_char_def fen_digit_value_def)
qed

lemma fen_chunk_piece_char:
  "fen_chunk (fen_piece_char p) = Some [Some p]"
  by (simp add: fen_chunk.simps fen_piece_of_char_piece_char)

definition parse_fen_rank :: "string => piece option list option" where
  "parse_fen_rank cs =
    (case parse_fen_rank_cells cs of
       Some xs => if length xs = 8 then Some xs else None
     | None => None)"

fun fen_split :: "char => string => string list" where
  "fen_split d [] = [[]]"
| "fen_split d (c#cs) =
    (if c = d then [] # fen_split d cs
     else (case fen_split d cs of
             [] => [[c]]
           | x#xs => (c#x)#xs))"

fun parse_fen_ranks :: "string list => piece option list list option" where
  "parse_fen_ranks [] = Some []"
| "parse_fen_ranks (x#xs) =
    (case parse_fen_rank x of
       None => None
     | Some row =>
         (case parse_fen_ranks xs of
            None => None
          | Some rows => Some (row#rows)))"

fun fen_update_row ::
    "board => rank => chess_file list => piece option list => board" where
  "fen_update_row b r [] [] = b"
| "fen_update_row b r (f#fs) (x#xs) =
    fen_update_row (board_update b (f,r) x) r fs xs"
| "fen_update_row b r _ _ = b"

lemma fen_update_row_overwrite:
  "fen_update_row b0 r all_files
      (map (\<lambda>f. b (f,r)) all_files) =
    (\<lambda>s :: square. if snd s = r then b s else b0 s)"
proof (rule board_ext)
  fix s :: square
  obtain f r' where "s = (f,r')"
    by (cases s) simp
  then show "fen_update_row b0 r all_files
      (map (\<lambda>f. b (f,r)) all_files) s =
      (\<lambda>s :: square. if snd s = r then b s else b0 s) s"
    by (cases f; cases r'; cases r;
      simp add: fen_update_row.simps all_files_def board_update_def)
qed

lemma fen_update_row_empty:
  "fen_update_row empty_board r all_files
      (map (\<lambda>f. b (f,r)) all_files) =
    (\<lambda>s :: square. if snd s = r then b s else None)"
proof (rule board_ext)
  fix s :: square
  obtain f r' where "s = (f,r')"
    by (cases s) simp
  then show "fen_update_row empty_board r all_files
      (map (\<lambda>f. b (f,r)) all_files) s =
      (\<lambda>s :: square. if snd s = r then b s else None) s"
    by (cases f; cases r'; cases r;
      simp add: fen_update_row.simps all_files_def empty_board_def board_update_def)
qed

fun fen_update_rows ::
    "board => rank list => piece option list list => board option" where
  "fen_update_rows b [] [] = Some b"
| "fen_update_rows b (r#rs) (row#rows) =
    (if length row = 8 then
       fen_update_rows (fen_update_row b r all_files row) rs rows
     else None)"
| "fen_update_rows b _ _ = None"

lemma fen_update_rows_board:
  "fen_update_rows empty_board fen_ranks
      (map (\<lambda>r. map (\<lambda>f. b (f,r)) all_files) fen_ranks) =
    Some b"
proof -
  have hlen: "length all_files = 8"
    by (simp add: all_files_def)
  have hfun:
      "(\<lambda>s :: square.
          if snd s = R1 then b s
          else if snd s = R2 then b s
          else if snd s = R3 then b s
          else if snd s = R4 then b s
          else if snd s = R5 then b s
          else if snd s = R6 then b s
          else if snd s = R7 then b s
          else if snd s = R8 then b s
          else empty_board s) = b"
    proof (rule board_ext)
      fix s :: square
      obtain f r' where hs: "s = (f,r')"
        by (cases s) simp
      then show "(\<lambda>s :: square.
          if snd s = R1 then b s
          else if snd s = R2 then b s
          else if snd s = R3 then b s
          else if snd s = R4 then b s
          else if snd s = R5 then b s
          else if snd s = R6 then b s
          else if snd s = R7 then b s
          else if snd s = R8 then b s
          else empty_board s) s = b s"
        by (cases r'; simp)
    qed
  show ?thesis
    unfolding fen_ranks_def
    by (simp add: fen_update_rows.simps fen_update_row_overwrite hlen hfun
        del: fen_update_row.simps)
qed

definition parse_fen_placement :: "string => board option" where
  "parse_fen_placement cs =
    (case parse_fen_ranks (fen_split (CHR ''/'') cs) of
       Some rows =>
         if length rows = 8 then fen_update_rows empty_board fen_ranks rows
         else None
     | None => None)"

fun fen_encode_cells :: "piece option list => nat => string" where
  "fen_encode_cells [] n =
    (if n = 0 then [] else [fen_digit_char n])"
| "fen_encode_cells (None#xs) n = fen_encode_cells xs (Suc n)"
| "fen_encode_cells (Some p#xs) n =
    (if n = 0 then [] else [fen_digit_char n]) @
      [fen_piece_char p] @ fen_encode_cells xs 0"

lemma parse_fen_rank_cells_fen_encode_cells:
  assumes hn: "n + length xs \<le> 8"
  shows "parse_fen_rank_cells (fen_encode_cells xs n) =
      Some (replicate n None @ xs)"
using hn
proof (induction xs arbitrary: n)
  case Nil
  show ?case
  proof (cases n)
    case 0
    show ?thesis by (simp add: 0 fen_encode_cells.simps(1))
  next
    case (Suc k)
    have hsk: "Suc k \<le> 8"
      using Nil.prems Suc by (simp add: Suc; arith)
    have hdigit:
        "fen_chunk (fen_digit_char (Suc k)) =
          Some (replicate (Suc k) None)"
      using fen_chunk_digit[of "Suc k"] hsk by simp
    show ?thesis
      using hdigit by (simp add: Suc fen_encode_cells.simps(1))
  qed
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case None
    have hsum: "Suc n + length xs \<le> 8"
      using Cons.prems by (simp add: add_Suc; arith)
    have ih:
        "parse_fen_rank_cells (fen_encode_cells xs (Suc n)) =
          Some (replicate (Suc n) None @ xs)"
      using Cons.IH[OF hsum] .
    have rep: "replicate n None @ [None] = None # replicate n None"
      by (induct n) simp_all
    show ?thesis
      using ih None rep by (simp add: fen_encode_cells.simps(2) rep[symmetric])
  next
    case (Some p)
    have hpre0: "0 + length xs \<le> 8"
      using Cons.prems by (simp add: add_Suc; arith)
    have hi0:
        "parse_fen_rank_cells (fen_encode_cells xs 0) = Some xs"
      using Cons.IH[OF hpre0] by simp
    have hpiece:
        "parse_fen_rank_cells [fen_piece_char p] = Some [Some p]"
      by (simp add: parse_fen_rank_cells.simps fen_chunk_piece_char
          del: fen_chunk.simps)
    have hptail:
        "parse_fen_rank_cells
            ([fen_piece_char p] @ fen_encode_cells xs 0) =
          Some (Some p # xs)"
      using parse_fen_rank_cells_append[of "[fen_piece_char p]"
          "fen_encode_cells xs 0"] hpiece hi0 by simp
    show ?thesis
    proof (cases n)
      case 0
      show ?thesis
        using hptail Some 0
        by (simp add: fen_encode_cells.simps(3))
    next
      case (Suc k)
      have hsk: "Suc k \<le> 8"
        using Cons.prems Suc by arith
      have hdigit:
          "parse_fen_rank_cells [fen_digit_char (Suc k)] =
            Some (replicate (Suc k) None)"
        using fen_chunk_digit[of "Suc k"] hsk
        by (simp add: parse_fen_rank_cells.simps)
      have hprefix:
          "parse_fen_rank_cells
              ([fen_digit_char (Suc k)] @
                ([fen_piece_char p] @ fen_encode_cells xs 0)) =
            Some (replicate (Suc k) None @ Some p # xs)"
        using parse_fen_rank_cells_append[of "[fen_digit_char (Suc k)]"
            "[fen_piece_char p] @ fen_encode_cells xs 0"] hdigit hptail
        by simp
      show ?thesis
        using hprefix Some Suc
        by (simp add: fen_encode_cells.simps(3))
    qed
  qed
qed

lemma fen_digit_char_not_slash:
  "CHR ''/'' \<noteq> fen_digit_char n"
  by (simp add: fen_digit_char_def split: if_splits)

lemma fen_piece_char_not_slash:
  "CHR ''/'' \<noteq> fen_piece_char p"
proof -
  obtain c k where hp: "p = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases p; simp)
  then show ?thesis
    by (cases c; cases k;
      simp add: fen_piece_char_def fen_piece_char_of_def)
qed

lemma fen_encode_cells_no_slash:
  "CHR ''/'' \<notin> set (fen_encode_cells (xs :: piece option list) (n :: nat))"
proof (induction xs arbitrary: n rule: list.induct)
  case Nil
  show ?case
    by (cases "n = 0";
      simp_all add: fen_digit_char_not_slash)
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case None
    then show ?thesis
      using Cons.IH[of "Suc n"] by (simp add: fen_digit_char_not_slash)
  next
    case (Some p)
    then show ?thesis
      using Cons.IH[of 0]
      by (simp add: fen_digit_char_not_slash fen_piece_char_not_slash)
  qed
qed

definition fen_rank_text :: "board => rank => string" where
  "fen_rank_text b r = fen_encode_cells (map (\<lambda>f. b (f,r)) all_files) 0"

lemma fen_rank_text_no_slash:
  "CHR ''/'' \<notin> set (fen_rank_text b r)"
  unfolding fen_rank_text_def
  using fen_encode_cells_no_slash
    [of "map (\<lambda>f. b (f,r)) all_files" 0]
  by simp

lemma fen_digit_char_not_space:
  "CHR '' '' \<noteq> fen_digit_char n"
  by (simp add: fen_digit_char_def split: if_splits)

lemma fen_piece_char_not_space:
  "CHR '' '' \<noteq> fen_piece_char p"
proof -
  obtain c k where hp: "p = \<lparr>piece_color = c, piece_kind = k\<rparr>"
    by (cases p; simp)
  then show ?thesis
    by (cases c; cases k;
      simp add: fen_piece_char_def fen_piece_char_of_def)
qed

lemma fen_encode_cells_no_space:
  "CHR '' '' \<notin> set (fen_encode_cells (xs :: piece option list) (n :: nat))"
proof (induction xs arbitrary: n rule: list.induct)
  case Nil
  show ?case
    by (cases "n = 0";
      simp_all add: fen_digit_char_not_space)
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case None
    then show ?thesis
      using Cons.IH[of "Suc n"] by (simp add: fen_digit_char_not_space)
  next
    case (Some p)
    then show ?thesis
      using Cons.IH[of 0]
      by (simp add: fen_digit_char_not_space fen_piece_char_not_space)
  qed
qed

lemma fen_rank_text_no_space:
  "CHR '' '' \<notin> set (fen_rank_text b r)"
  unfolding fen_rank_text_def
  using fen_encode_cells_no_space
    [of "map (\<lambda>f. b (f,r)) all_files" 0]
  by simp

lemma fen_nat_digits_no_space:
  "CHR '' '' \<notin> set (fen_nat_digits n)"
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (simp add: fen_nat_digits.simps fen_digit_char_not_space)
  next
    case False
    show ?thesis
    proof (cases "n < 10")
      case True
      then show ?thesis
        by (simp add: fen_nat_digits.simps fen_digit_char_not_space)
    next
      case False
      have hdiv: "n div 10 < n"
        using False by (simp add: div_less_iff_less_mult)
      have hi: "CHR '' '' \<notin> set (fen_nat_digits (n div 10))"
        using less.hyps[OF hdiv] .
      then show ?thesis
        by (simp add: fen_nat_digits.simps fen_digit_char_not_space)
    qed
  qed
qed

lemma parse_fen_rank_fen_rank_text:
  "parse_fen_rank (fen_rank_text b r) =
    Some (map (\<lambda>f. b (f,r)) all_files)"
proof -
  have h:
      "parse_fen_rank_cells
          (fen_encode_cells (map (\<lambda>f. b (f,r)) all_files) 0) =
        Some (map (\<lambda>f. b (f,r)) all_files)"
    using parse_fen_rank_cells_fen_encode_cells
      [of 0 "map (\<lambda>f. b (f,r)) all_files"]
    by (simp add: all_files_def)
  show ?thesis
    unfolding parse_fen_rank_def fen_rank_text_def
    using h by (simp add: all_files_def)
qed

fun fen_join_ranks :: "string list => string" where
  "fen_join_ranks [] = []"
| "fen_join_ranks [x] = x"
| "fen_join_ranks (x#xs) = x @ [CHR ''/''] @ fen_join_ranks xs"

lemma fen_split_no_delim:
  assumes hd: "d \<notin> set xs"
  shows "fen_split d xs = [xs]"
using hd
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons c xs)
  have hc: "c \<noteq> d"
    using Cons.prems by auto
  have hxs: "d \<notin> set xs"
    using Cons.prems by simp
  show ?case
    using Cons.IH[OF hxs] hc
    by (simp add: fen_split.simps)
qed

lemma fen_split_append_delim:
  assumes hd: "d \<notin> set xs"
  shows "fen_split d (xs @ [d] @ ys) = xs # fen_split d ys"
using hd
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons c xs)
  have hc: "c \<noteq> d"
    using Cons.prems(1) by auto
  have hxs: "d \<notin> set xs"
    using Cons.prems(1) by simp
  show ?case
    using Cons.IH[OF hxs] hc
    by (simp add: fen_split.simps)
qed

lemma fen_split_join_ranks:
  assumes hne: "xs \<noteq> []"
    and hno: "\<forall>x \<in> set xs. CHR ''/'' \<notin> set x"
  shows "fen_split (CHR ''/'') (fen_join_ranks xs) = xs"
using hne hno
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have hx: "CHR ''/'' \<notin> set x"
    using Cons.prems(2) by simp
  show ?case
  proof (cases xs)
    case Nil
    show ?thesis
      using fen_split_no_delim[OF hx] Nil
      by (simp add: fen_join_ranks.simps)
  next
    case (Cons y ys)
    have htail_ne: "y # ys \<noteq> []" by simp
    have htail_no: "\<forall>z \<in> set (y # ys). CHR ''/'' \<notin> set z"
      using Cons.prems(2) Cons by simp
    have htail_ne_old: "xs \<noteq> []"
      using Cons by simp
    have htail_no_old: "\<forall>z \<in> set xs. CHR ''/'' \<notin> set z"
      using Cons.prems(2) by simp
    have hi_old:
        "fen_split (CHR ''/'') (fen_join_ranks xs) = xs"
      using Cons.IH[OF htail_ne_old htail_no_old] .
    have hi:
        "fen_split (CHR ''/'') (fen_join_ranks (y # ys)) = y # ys"
      using hi_old Cons by simp
    show ?thesis
      using fen_split_append_delim[OF hx] hi Cons
      by (simp add: fen_join_ranks.simps)
  qed
qed

definition fen_placement :: "board => string" where
  "fen_placement b = fen_join_ranks (map (fen_rank_text b) fen_ranks)"

lemma fen_join_ranks_no_space:
  assumes hno: "\<forall>x \<in> set xs. CHR '' '' \<notin> set x"
  shows "CHR '' '' \<notin> set (fen_join_ranks xs)"
using hno
proof (induction xs)
  case Nil
  then show ?case by (simp add: fen_join_ranks.simps)
next
  case (Cons x xs)
  have hx: "CHR '' '' \<notin> set x"
    using Cons.prems by simp
  have htail: "\<forall>z \<in> set xs. CHR '' '' \<notin> set z"
    using Cons.prems by simp
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis using hx by (simp add: fen_join_ranks.simps)
  next
    case (Cons y ys)
    have hi: "CHR '' '' \<notin> set (fen_join_ranks (y # ys))"
      using Cons.IH[OF htail] Cons by simp
    then show ?thesis
      using hx Cons by (simp add: fen_join_ranks.simps)
  qed
qed

lemma fen_placement_no_space:
  "CHR '' '' \<notin> set (fen_placement b)"
proof -
  have hno:
      "\<forall>x \<in> set (map (fen_rank_text b) fen_ranks).
        CHR '' '' \<notin> set x"
    by (auto simp add: fen_rank_text_no_space)
  show ?thesis
    unfolding fen_placement_def
    by (rule fen_join_ranks_no_space[OF hno])
qed

lemma fen_split_fen_placement:
  "fen_split (CHR ''/'') (fen_placement b) =
    map (fen_rank_text b) fen_ranks"
proof -
  have hne: "map (fen_rank_text b) fen_ranks \<noteq> []"
    by (simp add: fen_ranks_def)
  have hno:
      "\<forall>x \<in> set (map (fen_rank_text b) fen_ranks).
        CHR ''/'' \<notin> set x"
    by (auto simp add: fen_rank_text_no_slash)
  show ?thesis
    unfolding fen_placement_def
    using fen_split_join_ranks[OF hne hno] .
qed

lemma parse_fen_ranks_fen_rank_text:
  "parse_fen_ranks (map (fen_rank_text b) fen_ranks) =
    Some (map (\<lambda>r. map (\<lambda>f. b (f,r)) all_files) fen_ranks)"
  unfolding fen_ranks_def
  by (simp add: parse_fen_ranks.simps parse_fen_rank_fen_rank_text)

lemma parse_fen_placement_fen_placement:
  "parse_fen_placement (fen_placement b) = Some b"
proof -
  have hs:
      "fen_split (CHR ''/'') (fen_placement b) =
        map (fen_rank_text b) fen_ranks"
    by (rule fen_split_fen_placement)
  have hr:
      "parse_fen_ranks (map (fen_rank_text b) fen_ranks) =
        Some (map (\<lambda>r. map (\<lambda>f. b (f,r)) all_files) fen_ranks)"
    by (rule parse_fen_ranks_fen_rank_text)
  have hu:
      "fen_update_rows empty_board fen_ranks
          (map (\<lambda>r. map (\<lambda>f. b (f,r)) all_files) fen_ranks) =
        Some b"
    by (rule fen_update_rows_board)
  have hlen:
      "length (map (\<lambda>r. map (\<lambda>f. b (f,r)) all_files) fen_ranks) = 8"
    by (simp add: fen_ranks_def)
  show ?thesis
    unfolding parse_fen_placement_def
    using hs hr hu hlen by simp
qed

definition fen_turn_text :: "color => string" where
  "fen_turn_text c = (case c of White => [CHR ''w''] | Black => [CHR ''b''])"

definition fen_castling_char :: "castle_right => char" where
  "fen_castling_char r =
    (case r of WhiteKingSide => CHR ''K'' | WhiteQueenSide => CHR ''Q'' |
       BlackKingSide => CHR ''k'' | BlackQueenSide => CHR ''q'')"

definition fen_castling_text :: "castling_rights => string" where
  "fen_castling_text R =
    (if R = {} then [CHR ''-''] else
      (if WhiteKingSide \<in> R then [CHR ''K''] else []) @
      (if WhiteQueenSide \<in> R then [CHR ''Q''] else []) @
      (if BlackKingSide \<in> R then [CHR ''k''] else []) @
      (if BlackQueenSide \<in> R then [CHR ''q''] else []))"

definition fen_ep_text :: "square option => string" where
  "fen_ep_text ep =
    (case ep of None => [CHR ''-'']
     | Some (f,r) => [fen_file_char f, fen_rank_char r])"

lemma fen_turn_text_no_space:
  "CHR '' '' \<notin> set (fen_turn_text c)"
  by (cases c; simp add: fen_turn_text_def)

lemma fen_castling_text_no_space:
  "CHR '' '' \<notin> set (fen_castling_text R)"
  by (simp add: fen_castling_text_def split: if_splits)

lemma fen_ep_text_no_space:
  "CHR '' '' \<notin> set (fen_ep_text ep)"
proof (cases ep)
  case None
  then show ?thesis by (simp add: fen_ep_text_def)
next
  case (Some s)
  obtain f r where hs: "s = (f,r)" by (cases s) simp
  then show ?thesis
    using Some by (cases f; cases r;
      simp add: fen_ep_text_def fen_file_char_def fen_rank_char_def)
qed

fun fen_join_fields :: "string list => string" where
  "fen_join_fields [] = []"
| "fen_join_fields [x] = x"
| "fen_join_fields (x#xs) = x @ [CHR '' ''] @ fen_join_fields xs"

lemma fen_split_join_fields:
  assumes hne: "xs \<noteq> []"
    and hno: "\<forall>x \<in> set xs. CHR '' '' \<notin> set x"
  shows "fen_split (CHR '' '') (fen_join_fields xs) = xs"
using hne hno
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have hx: "CHR '' '' \<notin> set x"
    using Cons.prems(2) by simp
  show ?case
  proof (cases xs)
    case Nil
    show ?thesis
      using fen_split_no_delim[OF hx] Nil
      by (simp add: fen_join_fields.simps)
  next
    case (Cons y ys)
    have htail_ne: "y # ys \<noteq> []" by simp
    have htail_no: "\<forall>z \<in> set (y # ys). CHR '' '' \<notin> set z"
      using Cons.prems(2) Cons by simp
    have htail_ne_old: "xs \<noteq> []"
      using Cons by simp
    have htail_no_old: "\<forall>z \<in> set xs. CHR '' '' \<notin> set z"
      using Cons.prems(2) by simp
    have hi_old:
        "fen_split (CHR '' '') (fen_join_fields xs) = xs"
      using Cons.IH[OF htail_ne_old htail_no_old] .
    have hi:
        "fen_split (CHR '' '') (fen_join_fields (y # ys)) = y # ys"
      using hi_old Cons by simp
    show ?thesis
      using fen_split_append_delim[OF hx] hi Cons
      by (simp add: fen_join_fields.simps)
  qed
qed

definition print_fen :: "position => fen_string" where
  "print_fen p =
    fen_placement (position_board p) @ [CHR '' ''] @
    fen_turn_text (position_turn p) @ [CHR '' ''] @
    fen_castling_text (position_castling p) @ [CHR '' ''] @
    fen_ep_text (position_en_passant p) @ [CHR '' ''] @
    fen_nat_digits (position_halfmove p) @ [CHR '' ''] @
    fen_nat_digits (position_fullmove p)"

lemma print_fen_fields:
  "print_fen p =
    fen_join_fields
      [fen_placement (position_board p),
       fen_turn_text (position_turn p),
       fen_castling_text (position_castling p),
       fen_ep_text (position_en_passant p),
       fen_nat_digits (position_halfmove p),
       fen_nat_digits (position_fullmove p)]"
  by (simp add: print_fen_def fen_join_fields.simps)

definition parse_fen_turn :: "string => color option" where
  "parse_fen_turn cs =
    (if cs = [CHR ''w''] then Some White else
     if cs = [CHR ''b''] then Some Black else None)"

lemma parse_fen_turn_fen_turn_text:
  "parse_fen_turn (fen_turn_text c) = Some c"
  by (cases c; simp add: parse_fen_turn_def fen_turn_text_def)

fun fen_castling_right_of_char :: "char => castle_right option" where
  "fen_castling_right_of_char c =
    (if c = CHR ''K'' then Some WhiteKingSide else
     if c = CHR ''Q'' then Some WhiteQueenSide else
     if c = CHR ''k'' then Some BlackKingSide else
     if c = CHR ''q'' then Some BlackQueenSide else None)"

fun fen_castling_valid :: "string => bool" where
  "fen_castling_valid [] = True"
| "fen_castling_valid (c#cs) =
    (case fen_castling_right_of_char c of
       None => False
     | Some r => c \<notin> set cs & fen_castling_valid cs)"

fun fen_castling_acc :: "string => castling_rights => castling_rights" where
  "fen_castling_acc [] R = R"
| "fen_castling_acc (c#cs) R =
    (case fen_castling_right_of_char c of
       None => R
     | Some r => fen_castling_acc cs (insert r R))"

definition parse_fen_castling :: "string => castling_rights option" where
  "parse_fen_castling cs =
    (if cs = [CHR ''-''] then Some {} else
     if cs = [] | ~ fen_castling_valid cs then None
     else Some (fen_castling_acc cs {}))"

lemma parse_fen_castling_flags:
  assumes hnonempty:
    "WhiteKingSide \<in> R \<or> WhiteQueenSide \<in> R \<or>
     BlackKingSide \<in> R \<or> BlackQueenSide \<in> R"
  shows
    "parse_fen_castling
      ((if WhiteKingSide \<in> R then [CHR ''K''] else []) @
       (if WhiteQueenSide \<in> R then [CHR ''Q''] else []) @
       (if BlackKingSide \<in> R then [CHR ''k''] else []) @
       (if BlackQueenSide \<in> R then [CHR ''q''] else [])) =
     Some ((if WhiteKingSide \<in> R then {WhiteKingSide} else {}) \<union>
       (if WhiteQueenSide \<in> R then {WhiteQueenSide} else {}) \<union>
       (if BlackKingSide \<in> R then {BlackKingSide} else {}) \<union>
       (if BlackQueenSide \<in> R then {BlackQueenSide} else {}))"
using hnonempty
  by (cases "WhiteKingSide \<in> R";
      cases "WhiteQueenSide \<in> R";
      cases "BlackKingSide \<in> R";
      cases "BlackQueenSide \<in> R";
      simp_all add: parse_fen_castling_def fen_castling_valid.simps
        fen_castling_acc.simps)

lemma parse_fen_castling_fen_castling_text:
  "parse_fen_castling (fen_castling_text R) = Some R"
proof -
  have hR:
      "R =
        (if WhiteKingSide \<in> R then {WhiteKingSide} else {}) \<union>
        (if WhiteQueenSide \<in> R then {WhiteQueenSide} else {}) \<union>
        (if BlackKingSide \<in> R then {BlackKingSide} else {}) \<union>
        (if BlackQueenSide \<in> R then {BlackQueenSide} else {})"
  proof (rule set_eqI)
    fix r
    show "r \<in> R \<longleftrightarrow>
      r \<in> (if WhiteKingSide \<in> R then {WhiteKingSide} else {}) \<union>
        (if WhiteQueenSide \<in> R then {WhiteQueenSide} else {}) \<union>
        (if BlackKingSide \<in> R then {BlackKingSide} else {}) \<union>
        (if BlackQueenSide \<in> R then {BlackQueenSide} else {})"
      by (cases r; simp)
  qed
  show ?thesis
  proof (cases "R = {}")
    case True
    then show ?thesis
      by (simp add: fen_castling_text_def parse_fen_castling_def)
  next
    case False
    have hnonempty:
        "WhiteKingSide \<in> R \<or> WhiteQueenSide \<in> R \<or>
         BlackKingSide \<in> R \<or> BlackQueenSide \<in> R"
    proof (rule ccontr)
      assume hn:
        "\<not> (WhiteKingSide \<in> R \<or> WhiteQueenSide \<in> R \<or>
          BlackKingSide \<in> R \<or> BlackQueenSide \<in> R)"
      have hzero: "R = {}"
        using hR hn by simp
      with False show False by simp
    qed
    have hf:
        "parse_fen_castling
          ((if WhiteKingSide \<in> R then [CHR ''K''] else []) @
           (if WhiteQueenSide \<in> R then [CHR ''Q''] else []) @
           (if BlackKingSide \<in> R then [CHR ''k''] else []) @
           (if BlackQueenSide \<in> R then [CHR ''q''] else [])) =
         Some ((if WhiteKingSide \<in> R then {WhiteKingSide} else {}) \<union>
           (if WhiteQueenSide \<in> R then {WhiteQueenSide} else {}) \<union>
           (if BlackKingSide \<in> R then {BlackKingSide} else {}) \<union>
           (if BlackQueenSide \<in> R then {BlackQueenSide} else {}))"
      by (rule parse_fen_castling_flags[OF hnonempty])
    have ht:
        "fen_castling_text R =
          (if WhiteKingSide \<in> R then [CHR ''K''] else []) @
           (if WhiteQueenSide \<in> R then [CHR ''Q''] else []) @
           (if BlackKingSide \<in> R then [CHR ''k''] else []) @
           (if BlackQueenSide \<in> R then [CHR ''q''] else [])"
      using False by (simp add: fen_castling_text_def)
    show ?thesis
      using hf ht hR by simp
  qed
qed

definition parse_fen_ep :: "string => square option option" where
  "parse_fen_ep cs =
    (if cs = [CHR ''-''] then Some None else
     case cs of
       [f,r] =>
         (case (fen_file_of_char f, fen_rank_of_char r) of
            (Some f', Some r') => Some (Some (f',r'))
          | _ => None)
     | _ => None)"

lemma parse_fen_ep_fen_ep_text:
  "parse_fen_ep (fen_ep_text ep) = Some ep"
proof (cases ep)
  case None
  then show ?thesis
    by (simp add: parse_fen_ep_def fen_ep_text_def)
next
  case (Some s)
  obtain f r where hs: "s = (f,r)"
    by (cases s) simp
  then show ?thesis using Some
    by (cases f; cases r;
      simp add: parse_fen_ep_def fen_ep_text_def
        fen_file_of_char_file_char fen_rank_of_char_rank_char)
qed

fun fen_parse_nat_acc :: "nat => string => nat option" where
  "fen_parse_nat_acc n [] = Some n"
| "fen_parse_nat_acc n (c#cs) =
    (case c of
       _ =>
         (case (if c = CHR ''0'' then Some 0 else
                if c = CHR ''1'' then Some 1 else
                if c = CHR ''2'' then Some 2 else
                if c = CHR ''3'' then Some 3 else
                if c = CHR ''4'' then Some 4 else
                if c = CHR ''5'' then Some 5 else
                if c = CHR ''6'' then Some 6 else
                if c = CHR ''7'' then Some 7 else
                if c = CHR ''8'' then Some 8 else
                if c = CHR ''9'' then Some 9 else None) of
           None => None
         | Some d => fen_parse_nat_acc (10*n+d) cs))"

definition parse_fen_nat :: "string => nat option" where
  "parse_fen_nat cs =
    (if cs = [] then None else fen_parse_nat_acc 0 cs)"

lemma fen_parse_nat_acc_append:
  "fen_parse_nat_acc n (xs @ ys) =
    (case fen_parse_nat_acc n xs of
       None => None
     | Some z => fen_parse_nat_acc z ys)"
  by (induct xs arbitrary: n) (simp_all split: option.splits)

lemma fen_parse_nat_acc_digit:
  assumes "d \<le> 9"
  shows "fen_parse_nat_acc n [fen_digit_char d] = Some (10 * n + d)"
proof -
  have hd:
      "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
       d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using assms by arith
  then show ?thesis
    by (elim disjE; simp add: fen_parse_nat_acc.simps fen_digit_char_def)
qed

lemma fen_nat_digits_nonempty:
  "fen_nat_digits n \<noteq> []"
proof (cases n)
  case 0
  then show ?thesis by (simp add: fen_nat_digits.simps)
next
  case (Suc k)
  then show ?thesis
    by (simp add: fen_nat_digits.simps split: if_splits)
qed

lemma parse_fen_nat_fen_nat_digits:
  "parse_fen_nat (fen_nat_digits n) = Some n"
proof (induct n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (simp add: parse_fen_nat_def fen_nat_digits.simps
          fen_parse_nat_acc.simps)
  next
    case False
    show ?thesis
    proof (cases "n < 10")
      case True
      have hd:
          "fen_parse_nat_acc 0 [fen_digit_char n] = Some n"
        using fen_parse_nat_acc_digit[of n 0] True by simp
      have hdigits: "fen_nat_digits n = [fen_digit_char n]"
        using True False by (simp add: fen_nat_digits.simps)
      have hne: "[fen_digit_char n] \<noteq> []" by simp
      then show ?thesis
        using hd False
        unfolding parse_fen_nat_def
        by (simp only: hdigits if_not_P[OF hne] if_False)
    next
      case False
      have hn10: "10 \<le> n"
        using False by arith
      have hdiv: "n div 10 < n"
        using hn10 by (simp add: div_less_iff_less_mult)
        have ih:
          "parse_fen_nat (fen_nat_digits (n div 10)) =
            Some (n div 10)"
        using less.hyps[OF hdiv] .
      have hi:
          "fen_parse_nat_acc 0 (fen_nat_digits (n div 10)) =
            Some (n div 10)"
      proof -
        have hne0: "fen_nat_digits (n div 10) \<noteq> []"
          by (rule fen_nat_digits_nonempty)
        show ?thesis
          using ih
          unfolding parse_fen_nat_def
          by (simp only: if_not_P[OF hne0] if_False)
      qed
      have hd:
          "fen_parse_nat_acc (n div 10)
              [fen_digit_char (n mod 10)] =
            Some (10 * (n div 10) + (n mod 10))"
        using fen_parse_nat_acc_digit[of "n mod 10" "n div 10"]
          by (simp add: mod_less_divisor)
      have hdecomp:
          "fen_nat_digits n =
            fen_nat_digits (n div 10) @
              [fen_digit_char (n mod 10)]"
        using hn10 by (simp add: fen_nat_digits.simps)
      have hn:
          "10 * (n div 10) + (n mod 10) = n"
        by (simp add: div_mult_mod_eq mult.commute)
      have hacc:
          "fen_parse_nat_acc 0 (fen_nat_digits n) = Some n"
      proof -
        show ?thesis
          using hdecomp hi hd hn
          by (simp add: fen_parse_nat_acc_append)
      qed
      show ?thesis
      proof -
        have hne: "fen_nat_digits n \<noteq> []"
          by (rule fen_nat_digits_nonempty)
        show ?thesis
          using hacc
          unfolding parse_fen_nat_def
          by (simp only: if_not_P[OF hne] if_False)
      qed
    qed
  qed
qed

definition parse_fen :: "fen_string => position option" where
  "parse_fen cs =
    (case fen_split (CHR '' '') cs of
       [placement, turn, castling, ep, halfmove, fullmove] =>
         (case (parse_fen_placement placement, parse_fen_turn turn,
                parse_fen_castling castling, parse_fen_ep ep,
                parse_fen_nat halfmove, parse_fen_nat fullmove) of
            (Some b, Some c, Some R, Some ep', Some hm, Some fm) =>
              if fm = 0 then None
              else Some \<lparr>position_board = b, position_turn = c,
                position_castling = R, position_en_passant = ep',
                position_halfmove = hm, position_fullmove = fm\<rparr>
          | _ => None)
     | _ => None)"

definition fen_text_well_formed :: "fen_string => bool" where
  "fen_text_well_formed s \<longleftrightarrow> parse_fen s \<noteq> None"

lemma parse_fen_print_fen_position:
  assumes hfm: "position_fullmove p > 0"
  shows "parse_fen (print_fen p) = Some p"
proof -
  let ?fs =
    "[fen_placement (position_board p),
      fen_turn_text (position_turn p),
      fen_castling_text (position_castling p),
      fen_ep_text (position_en_passant p),
      fen_nat_digits (position_halfmove p),
      fen_nat_digits (position_fullmove p)]"
  have hne: "?fs \<noteq> []"
    by simp
  have hno: "\<forall>x \<in> set ?fs. CHR '' '' \<notin> set x"
  proof
    fix x
    assume hx: "x \<in> set ?fs"
    have hx':
        "x = fen_placement (position_board p) \<or>
         x = fen_turn_text (position_turn p) \<or>
         x = fen_castling_text (position_castling p) \<or>
         x = fen_ep_text (position_en_passant p) \<or>
         x = fen_nat_digits (position_halfmove p) \<or>
         x = fen_nat_digits (position_fullmove p)"
      using hx by (auto simp only: set_simps insert_iff empty_iff)
    then show "CHR '' '' \<notin> set x"
    proof (elim disjE)
      assume hx1: "x = fen_placement (position_board p)"
      show ?thesis
        using hx1 fen_placement_no_space by blast
    next
      assume hx2: "x = fen_turn_text (position_turn p)"
      show ?thesis
        using hx2 fen_turn_text_no_space by blast
    next
      assume hx3: "x = fen_castling_text (position_castling p)"
      show ?thesis
        using hx3 fen_castling_text_no_space by blast
    next
      assume hx4: "x = fen_ep_text (position_en_passant p)"
      show ?thesis
        using hx4 fen_ep_text_no_space by blast
    next
      assume hx5: "x = fen_nat_digits (position_halfmove p)"
      show ?thesis
        using hx5 fen_nat_digits_no_space by blast
    next
      assume hx6: "x = fen_nat_digits (position_fullmove p)"
      show ?thesis
        using hx6 fen_nat_digits_no_space by blast
    qed
  qed
  have hs:
      "fen_split (CHR '' '') (print_fen p) = ?fs"
  proof -
    have hp: "print_fen p = fen_join_fields ?fs"
      by (simp add: print_fen_fields)
    show ?thesis
      using hp fen_split_join_fields[OF hne hno] by simp
  qed
  have hplacement:
      "parse_fen_placement (fen_placement (position_board p)) =
        Some (position_board p)"
    by (rule parse_fen_placement_fen_placement)
  have hturn:
      "parse_fen_turn (fen_turn_text (position_turn p)) =
        Some (position_turn p)"
    by (rule parse_fen_turn_fen_turn_text)
  have hcastling:
      "parse_fen_castling (fen_castling_text (position_castling p)) =
        Some (position_castling p)"
    by (rule parse_fen_castling_fen_castling_text)
  have hep:
      "parse_fen_ep (fen_ep_text (position_en_passant p)) =
        Some (position_en_passant p)"
    by (rule parse_fen_ep_fen_ep_text)
  have hhalf:
      "parse_fen_nat (fen_nat_digits (position_halfmove p)) =
        Some (position_halfmove p)"
    by (rule parse_fen_nat_fen_nat_digits)
  have hfull:
      "parse_fen_nat (fen_nat_digits (position_fullmove p)) =
        Some (position_fullmove p)"
    by (rule parse_fen_nat_fen_nat_digits)
  have hfm0: "position_fullmove p \<noteq> 0"
    using hfm by arith
  show ?thesis
    unfolding parse_fen_def
    using hs hplacement hturn hcastling hep hhalf hfull hfm0
    by simp
qed

lemma print_fen_initial:
  "print_fen initial_position =
    ''rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1''"
  by eval

lemma parse_fen_print_fen:
  "parse_fen (print_fen initial_position) \<noteq> None"
  by eval

end
