section \<open>Chess moves\<close>

theory Chess_Move
  imports Chess_Position
begin

text \<open>
  Castling is represented by four constructors rather than by a disguised
  king move.  This keeps the wire-level move universe finite and makes the
  exceptional transition rules explicit.
\<close>

datatype promotion_kind =
    PromoteQueen
  | PromoteRook
  | PromoteBishop
  | PromoteKnight

datatype move =
    Normal square square
  | Promotion square square promotion_kind
  | EnPassant square square
  | WhiteKingCastle
  | WhiteQueenCastle
  | BlackKingCastle
  | BlackQueenCastle

fun promotion_piece_kind :: "promotion_kind \<Rightarrow> piece_kind" where
  "promotion_piece_kind PromoteQueen = Queen"
| "promotion_piece_kind PromoteRook = Rook"
| "promotion_piece_kind PromoteBishop = Bishop"
| "promotion_piece_kind PromoteKnight = Knight"

definition all_promotion_kinds :: "promotion_kind list" where
  "all_promotion_kinds =
    [PromoteQueen, PromoteRook, PromoteBishop, PromoteKnight]"

fun move_source :: "move \<Rightarrow> square" where
  "move_source (Normal s t) = s"
| "move_source (Promotion s t k) = s"
| "move_source (EnPassant s t) = s"
| "move_source WhiteKingCastle = (E, R1)"
| "move_source WhiteQueenCastle = (E, R1)"
| "move_source BlackKingCastle = (E, R8)"
| "move_source BlackQueenCastle = (E, R8)"

fun move_destination :: "move \<Rightarrow> square" where
  "move_destination (Normal s t) = t"
| "move_destination (Promotion s t k) = t"
| "move_destination (EnPassant s t) = t"
| "move_destination WhiteKingCastle = (G, R1)"
| "move_destination WhiteQueenCastle = (C, R1)"
| "move_destination BlackKingCastle = (G, R8)"
| "move_destination BlackQueenCastle = (C, R8)"

fun move_promotion :: "move \<Rightarrow> promotion_kind option" where
  "move_promotion (Promotion s t k) = Some k"
| "move_promotion _ = None"

fun is_castle :: "move \<Rightarrow> bool" where
  "is_castle WhiteKingCastle = True"
| "is_castle WhiteQueenCastle = True"
| "is_castle BlackKingCastle = True"
| "is_castle BlackQueenCastle = True"
| "is_castle _ = False"

fun is_en_passant :: "move \<Rightarrow> bool" where
  "is_en_passant (EnPassant s t) = True"
| "is_en_passant _ = False"

definition square_pairs :: "(square \<times> square) list" where
  "square_pairs = List.product all_squares all_squares"

definition ordinary_candidates :: "move list" where
  "ordinary_candidates =
    map (\<lambda>x. Normal (fst x) (snd x)) square_pairs"

definition promotion_candidates :: "move list" where
  "promotion_candidates =
    map (\<lambda>x. Promotion (fst (fst x)) (snd (fst x)) (snd x))
      (List.product square_pairs all_promotion_kinds)"

definition en_passant_candidates :: "move list" where
  "en_passant_candidates =
    map (\<lambda>x. EnPassant (fst x) (snd x)) square_pairs"

definition castle_candidates :: "move list" where
  "castle_candidates =
    [WhiteKingCastle, WhiteQueenCastle, BlackKingCastle, BlackQueenCastle]"

definition candidate_moves :: "move list" where
  "candidate_moves =
    ordinary_candidates @ promotion_candidates @
    en_passant_candidates @ castle_candidates"

lemma square_pairs_member:
  "(s,t) \<in> set square_pairs"
  by (auto simp: square_pairs_def all_squares_set)

lemma all_promotion_kinds_set:
  "set all_promotion_kinds = UNIV"
proof (rule set_eqI)
  fix k
  show "k \<in> set all_promotion_kinds \<longleftrightarrow> k \<in> UNIV"
    by (cases k; simp add: all_promotion_kinds_def)
qed

lemma normal_candidate_member:
  "Normal s t \<in> set ordinary_candidates"
proof -
  have hpair: "(s,t) \<in> set square_pairs"
    by (rule square_pairs_member)
  have map_set:
      "set (map (\<lambda>x. Normal (fst x) (snd x)) square_pairs) =
        Set.image (\<lambda>x. Normal (fst x) (snd x)) (set square_pairs)"
    by (rule List.set_map)
  have himg:
      "(\<lambda>x. Normal (fst x) (snd x)) (s,t) \<in>
        Set.image (\<lambda>x. Normal (fst x) (snd x)) (set square_pairs)"
    by (rule imageI; rule hpair)
  have hmap:
      "Normal s t \<in>
        set (map (\<lambda>x. Normal (fst x) (snd x)) square_pairs)"
    using himg map_set by (simp add: map_set)
  then show ?thesis by (simp add: ordinary_candidates_def)
qed

lemma en_passant_candidate_member:
  "EnPassant s t \<in> set en_passant_candidates"
proof -
  have hpair: "(s,t) \<in> set square_pairs"
    by (rule square_pairs_member)
  have map_set:
      "set (map (\<lambda>x. EnPassant (fst x) (snd x)) square_pairs) =
        Set.image (\<lambda>x. EnPassant (fst x) (snd x)) (set square_pairs)"
    by (rule List.set_map)
  have himg:
      "(\<lambda>x. EnPassant (fst x) (snd x)) (s,t) \<in>
        Set.image (\<lambda>x. EnPassant (fst x) (snd x)) (set square_pairs)"
    by (rule imageI; rule hpair)
  have hmap:
      "EnPassant s t \<in>
        set (map (\<lambda>x. EnPassant (fst x) (snd x)) square_pairs)"
    using himg map_set by (simp add: map_set)
  then show ?thesis by (simp add: en_passant_candidates_def)
qed

lemma promotion_candidate_member:
  "Promotion s t k \<in> set promotion_candidates"
proof -
  have hpair: "(s,t) \<in> set square_pairs"
    by (rule square_pairs_member)
  have hkind: "k \<in> set all_promotion_kinds"
    by (simp add: all_promotion_kinds_set)
  have hprod: "((s,t),k) \<in> set (List.product square_pairs all_promotion_kinds)"
    by (simp add: hpair hkind)
  have map_set:
      "set (map (\<lambda>x. Promotion (fst (fst x)) (snd (fst x)) (snd x))
          (List.product square_pairs all_promotion_kinds)) =
        Set.image (\<lambda>x. Promotion (fst (fst x)) (snd (fst x)) (snd x))
          (set (List.product square_pairs all_promotion_kinds))"
    by (rule List.set_map)
  have himg:
      "(\<lambda>x. Promotion (fst (fst x)) (snd (fst x)) (snd x)) ((s,t),k) \<in>
        Set.image (\<lambda>x. Promotion (fst (fst x)) (snd (fst x)) (snd x))
          (set (List.product square_pairs all_promotion_kinds))"
    by (rule imageI; rule hprod)
  then show ?thesis
    by (simp add: promotion_candidates_def map_set)
qed

lemma candidate_moves_complete:
  "set candidate_moves = UNIV"
proof (rule set_eqI)
  fix m
  show "m \<in> set candidate_moves \<longleftrightarrow> m \<in> UNIV"
  by (cases m;
      simp add: candidate_moves_def normal_candidate_member
        promotion_candidate_member en_passant_candidate_member
        castle_candidates_def)
qed

lemma move_distinct_cases:
  "Normal s t \<noteq> Promotion u v k \<and>
   Normal s t \<noteq> EnPassant u v \<and>
   Normal s t \<noteq> WhiteKingCastle \<and>
   Promotion s t k \<noteq> EnPassant u v \<and>
   Promotion s t k \<noteq> WhiteKingCastle \<and>
   EnPassant s t \<noteq> WhiteKingCastle"
  by simp_all

end
