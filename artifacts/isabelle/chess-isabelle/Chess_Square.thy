section \<open>Finite chessboard coordinates\<close>

theory Chess_Square
  imports Main
begin

datatype color = White | Black

fun opponent :: "color \<Rightarrow> color" where
  "opponent White = Black"
| "opponent Black = White"

datatype piece_kind = King | Queen | Rook | Bishop | Knight | Pawn

datatype chess_file = A | B | C | D | E | F | G | H
datatype rank = R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8

type_synonym square = "chess_file \<times> rank"

record piece =
  piece_color :: color
  piece_kind :: piece_kind

definition all_files :: "chess_file list" where
  "all_files = [A, B, C, D, E, F, G, H]"

definition all_ranks :: "rank list" where
  "all_ranks = [R1, R2, R3, R4, R5, R6, R7, R8]"

definition all_squares :: "square list" where
  "all_squares = concat (map (\<lambda>f. map (Pair f) all_ranks) all_files)"

definition file_index :: "chess_file \<Rightarrow> nat" where
  "file_index f = (case f of A \<Rightarrow> 0 | B \<Rightarrow> 1 | C \<Rightarrow> 2 |
      D \<Rightarrow> 3 | E \<Rightarrow> 4 | F \<Rightarrow> 5 | G \<Rightarrow> 6 | H \<Rightarrow> 7)"

definition rank_index :: "rank \<Rightarrow> nat" where
  "rank_index r = (case r of R1 \<Rightarrow> 0 | R2 \<Rightarrow> 1 | R3 \<Rightarrow> 2 |
      R4 \<Rightarrow> 3 | R5 \<Rightarrow> 4 | R6 \<Rightarrow> 5 | R7 \<Rightarrow> 6 | R8 \<Rightarrow> 7)"

definition coords :: "square \<Rightarrow> nat \<times> nat" where
  "coords s = (file_index (fst s), rank_index (snd s))"

definition file_of_index :: "nat \<Rightarrow> chess_file option" where
  "file_of_index n = (if n = 0 then Some A else if n = 1 then Some B else
     if n = 2 then Some C else if n = 3 then Some D else if n = 4 then Some E
     else if n = 5 then Some F else if n = 6 then Some G else
     if n = 7 then Some H else None)"

definition rank_of_index :: "nat \<Rightarrow> rank option" where
  "rank_of_index n = (if n = 0 then Some R1 else if n = 1 then Some R2 else
     if n = 2 then Some R3 else if n = 3 then Some R4 else if n = 4 then Some R5
     else if n = 5 then Some R6 else if n = 6 then Some R7 else
     if n = 7 then Some R8 else None)"

definition square_of_coords :: "nat \<times> nat \<Rightarrow> square option" where
  "square_of_coords p = (case p of (f, r) \<Rightarrow>
     case file_of_index f of None \<Rightarrow> None | Some f' \<Rightarrow>
       case rank_of_index r of None \<Rightarrow> None | Some r' \<Rightarrow> Some (f', r'))"

lemma all_files_set: "set all_files = UNIV"
proof (rule set_eqI)
  fix f
  show "f \<in> set all_files \<longleftrightarrow> f \<in> UNIV"
    by (cases f; simp add: all_files_def)
qed

lemma all_ranks_set: "set all_ranks = UNIV"
proof (rule set_eqI)
  fix r
  show "r \<in> set all_ranks \<longleftrightarrow> r \<in> UNIV"
    by (cases r; simp add: all_ranks_def)
qed

lemma pair_range_UNIV: "(\<Union>f :: chess_file. range (Pair f)) = UNIV"
  by auto

lemma all_squares_set: "set all_squares = UNIV"
  by (simp add: all_squares_def all_files_set all_ranks_set pair_range_UNIV)

lemma all_files_distinct: "distinct all_files"
  by (simp add: all_files_def)

lemma all_ranks_distinct: "distinct all_ranks"
  by (simp add: all_ranks_def)

lemma all_squares_distinct: "distinct all_squares"
  unfolding all_squares_def all_files_def all_ranks_def
  by (simp add: distinct_concat)

lemma all_squares_length: "length all_squares = 64"
  by (simp add: all_squares_def all_files_def all_ranks_def)

lemma all_squares_correct:
  "set all_squares = UNIV \<and> distinct all_squares \<and>
   length all_squares = 64"
  by (simp add: all_squares_set all_squares_distinct all_squares_length)

lemma file_index_cases: "file_index A = 0" "file_index B = 1"
    "file_index C = 2" "file_index D = 3" "file_index E = 4"
    "file_index F = 5" "file_index G = 6" "file_index H = 7"
  by (simp_all add: file_index_def)

lemma rank_index_cases: "rank_index R1 = 0" "rank_index R2 = 1"
    "rank_index R3 = 2" "rank_index R4 = 3" "rank_index R5 = 4"
    "rank_index R6 = 5" "rank_index R7 = 6" "rank_index R8 = 7"
  by (simp_all add: rank_index_def)

lemma square_of_coords_coords: "square_of_coords (coords s) = Some s"
  by (cases s; simp_all add: coords_def file_index_def rank_index_def
      square_of_coords_def file_of_index_def rank_of_index_def
      split: chess_file.splits rank.splits)

lemma file_index_lt: "file_index f < 8"
  by (cases f; simp add: file_index_def)

lemma rank_index_lt: "rank_index r < 8"
  by (cases r; simp add: rank_index_def)

lemma coords_in_bounds:
  "fst (coords s) < 8" "snd (coords s) < 8"
proof -
  have h1: "file_index (fst s) < 8" by (rule file_index_lt)
  have h2: "rank_index (snd s) < 8" by (rule rank_index_lt)
  show "fst (coords s) < 8" "snd (coords s) < 8"
    unfolding coords_def using h1 h2 by simp_all
qed

lemma coords_injective: "coords s = coords t \<Longrightarrow> s = t"
  by (metis option.inject square_of_coords_coords)

lemma opponent_involutive: "opponent (opponent c) = c"
  by (cases c) simp_all

lemma color_cases: "c = White \<or> c = Black"
  by (cases c) simp_all

lemma promotion_kinds: "set [Queen, Rook, Bishop, Knight] =
    {Queen, Rook, Bishop, Knight}"
  by simp

end
