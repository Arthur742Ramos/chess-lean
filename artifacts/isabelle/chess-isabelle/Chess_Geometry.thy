section \<open>Chess movement geometry\<close>

theory Chess_Geometry
  imports Chess_Position
begin

definition same_file :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "same_file s t \<longleftrightarrow> fst s = fst t"

definition same_rank :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "same_rank s t \<longleftrightarrow> snd s = snd t"

definition same_diagonal :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "same_diagonal s t \<longleftrightarrow>
    int (file_index (fst s)) - int (file_index (fst t)) =
      int (rank_index (snd s)) - int (rank_index (snd t)) \<or>
    int (file_index (fst s)) - int (file_index (fst t)) =
      - (int (rank_index (snd s)) - int (rank_index (snd t)))"

definition rook_geometry :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "rook_geometry s t \<longleftrightarrow> s \<noteq> t \<and> (same_file s t \<or> same_rank s t)"

definition bishop_geometry :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "bishop_geometry s t \<longleftrightarrow> s \<noteq> t \<and> same_diagonal s t"

definition queen_geometry :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "queen_geometry s t \<longleftrightarrow> rook_geometry s t \<or> bishop_geometry s t"

definition knight_geometry :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "knight_geometry s t \<longleftrightarrow>
    sorted_list_of_set {abs (int (file_index (fst s)) - int (file_index (fst t))),
      abs (int (rank_index (snd s)) - int (rank_index (snd t)))} = [1, 2]"

definition king_geometry :: "square \<Rightarrow> square \<Rightarrow> bool" where
  "king_geometry s t \<longleftrightarrow>
    max (abs (int (file_index (fst s)) - int (file_index (fst t))))
        (abs (int (rank_index (snd s)) - int (rank_index (snd t)))) = 1"

definition pawn_move_geometry :: "color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "pawn_move_geometry c s t \<longleftrightarrow>
    fst s = fst t \<and>
    ((c = White \<and> rank_index (snd t) = rank_index (snd s) + 1) \<or>
     (c = Black \<and> rank_index (snd s) = rank_index (snd t) + 1))"

definition pawn_attack_geometry :: "color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "pawn_attack_geometry c s t \<longleftrightarrow>
    abs (int (file_index (fst s)) - int (file_index (fst t))) = 1 \<and>
    ((c = White \<and> rank_index (snd t) = rank_index (snd s) + 1) \<or>
     (c = Black \<and> rank_index (snd s) = rank_index (snd t) + 1))"

definition pawn_double_geometry :: "color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "pawn_double_geometry c s t \<longleftrightarrow>
    fst s = fst t \<and>
    ((c = White \<and> snd s = R2 \<and> snd t = R4) \<or>
     (c = Black \<and> snd s = R7 \<and> snd t = R5))"

definition piece_geometry ::
    "piece_kind \<Rightarrow> color \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "piece_geometry k c s t \<longleftrightarrow>
    (case k of
       Rook \<Rightarrow> rook_geometry s t
     | Bishop \<Rightarrow> bishop_geometry s t
     | Queen \<Rightarrow> queen_geometry s t
     | Knight \<Rightarrow> knight_geometry s t
     | King \<Rightarrow> king_geometry s t
     | Pawn \<Rightarrow> pawn_move_geometry c s t)"

definition between :: "square \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "between s u t \<longleftrightarrow>
    u \<noteq> s \<and> u \<noteq> t \<and>
    ((same_file s t \<and> same_file s u \<and>
       ((rank_index (snd s) < rank_index (snd u) \<and> rank_index (snd u) < rank_index (snd t)) \<or>
        (rank_index (snd t) < rank_index (snd u) \<and> rank_index (snd u) < rank_index (snd s)))) \<or>
     (same_rank s t \<and> same_rank s u \<and>
       ((file_index (fst s) < file_index (fst u) \<and> file_index (fst u) < file_index (fst t)) \<or>
        (file_index (fst t) < file_index (fst u) \<and> file_index (fst u) < file_index (fst s)))) \<or>
     (same_diagonal s t \<and> same_diagonal s u \<and>
       (((int (file_index (fst s)) < int (file_index (fst u)) \<and>
          int (file_index (fst u)) < int (file_index (fst t))) \<or>
         (int (file_index (fst t)) < int (file_index (fst u)) \<and>
          int (file_index (fst u)) < int (file_index (fst s)))) \<and>
        ((int (rank_index (snd s)) < int (rank_index (snd u)) \<and>
          int (rank_index (snd u)) < int (rank_index (snd t))) \<or>
         (int (rank_index (snd t)) < int (rank_index (snd u)) \<and>
          int (rank_index (snd u)) < int (rank_index (snd s)))))))"

definition squares_between :: "square \<Rightarrow> square \<Rightarrow> square list" where
  "squares_between s t = filter (\<lambda>u. between s u t) all_squares"

definition clear_between :: "board \<Rightarrow> square \<Rightarrow> square \<Rightarrow> bool" where
  "clear_between b s t \<longleftrightarrow> (\<forall>u \<in> set (squares_between s t). b u = None)"

lemma between_member:
  "u \<in> set (squares_between s t) \<longleftrightarrow> between s u t"
  by (simp add: squares_between_def all_squares_set)

lemma squares_between_correct:
  "u \<in> set (squares_between s t) \<longleftrightarrow> between s u t"
  by (rule between_member)

lemma squares_between_endpoints:
  "s \<notin> set (squares_between s t)"
  "t \<notin> set (squares_between s t)"
  by (simp_all add: between_member between_def)

lemma same_file_refl: "same_file s s"
  by (simp add: same_file_def)

lemma same_rank_refl: "same_rank s s"
  by (simp add: same_rank_def)

end
