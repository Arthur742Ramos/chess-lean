section \<open>Board reflection symmetry\<close>

theory Chess_Symmetry
  imports Chess_Game Chess_Perft Chess_Transition
begin

fun mirror_rank :: "rank \<Rightarrow> rank" where
  "mirror_rank R1 = R8"
| "mirror_rank R2 = R7"
| "mirror_rank R3 = R6"
| "mirror_rank R4 = R5"
| "mirror_rank R5 = R4"
| "mirror_rank R6 = R3"
| "mirror_rank R7 = R2"
| "mirror_rank R8 = R1"

definition mirror_square :: "square \<Rightarrow> square" where
  "mirror_square s = (fst s, mirror_rank (snd s))"

definition mirror_piece :: "piece \<Rightarrow> piece" where
  "mirror_piece q =
    \<lparr>piece_color = opponent (piece_color q),
     piece_kind = piece_kind q\<rparr>"

definition mirror_board :: "board \<Rightarrow> board" where
  "mirror_board b s =
    (case b (mirror_square s) of None \<Rightarrow> None | Some q \<Rightarrow> Some (mirror_piece q))"

fun mirror_right :: "castle_right \<Rightarrow> castle_right" where
  "mirror_right WhiteKingSide = BlackKingSide"
| "mirror_right WhiteQueenSide = BlackQueenSide"
| "mirror_right BlackKingSide = WhiteKingSide"
| "mirror_right BlackQueenSide = WhiteQueenSide"

definition mirror_rights :: "castling_rights \<Rightarrow> castling_rights" where
  "mirror_rights R = Set.image mirror_right R"

fun mirror_move :: "move \<Rightarrow> move" where
  "mirror_move (Normal s t) = Normal (mirror_square s) (mirror_square t)"
| "mirror_move (Promotion s t k) =
     Promotion (mirror_square s) (mirror_square t) k"
| "mirror_move (EnPassant s t) =
     EnPassant (mirror_square s) (mirror_square t)"
| "mirror_move WhiteKingCastle = BlackKingCastle"
| "mirror_move WhiteQueenCastle = BlackQueenCastle"
| "mirror_move BlackKingCastle = WhiteKingCastle"
| "mirror_move BlackQueenCastle = WhiteQueenCastle"

definition mirror_position :: "position \<Rightarrow> position" where
  "mirror_position p =
    \<lparr>position_board = mirror_board (position_board p),
     position_turn = opponent (position_turn p),
     position_castling = mirror_rights (position_castling p),
     position_en_passant = map_option mirror_square (position_en_passant p),
     position_halfmove = position_halfmove p,
     position_fullmove = position_fullmove p\<rparr>"

lemma mirror_rank_involutive:
  "mirror_rank (mirror_rank r) = r"
  by (cases r; simp)

lemma mirror_rank_eq_iff:
  "mirror_rank r = mirror_rank s \<longleftrightarrow> r = s"
proof
  assume h: "mirror_rank r = mirror_rank s"
  have "mirror_rank (mirror_rank r) =
      mirror_rank (mirror_rank s)"
    using h by simp
  then show "r = s"
    by (simp add: mirror_rank_involutive)
next
  assume "r = s"
  then show "mirror_rank r = mirror_rank s" by simp
qed

lemma rank_index_mirror:
  "rank_index (mirror_rank r) = 7 - rank_index r"
  by (cases r; simp add: rank_index_def mirror_rank.simps)

lemma int_rank_index_mirror_diff:
  "int (7 - rank_index r) - int (7 - rank_index s) =
    - (int (rank_index r) - int (rank_index s))"
  by (cases r; cases s; simp add: rank_index_def)

lemma abs_int_rank_index_mirror_diff:
  "abs (int (7 - rank_index r) - int (7 - rank_index s)) =
    abs (int (rank_index r) - int (rank_index s))"
  by (cases r; cases s; simp add: rank_index_def)

lemma nat_rank_index_mirror_suc:
  "7 - rank_index r = Suc (7 - rank_index s) \<longleftrightarrow>
    rank_index s = Suc (rank_index r)"
  by (cases r; cases s; simp add: rank_index_def)

lemma rank_index_mirror_less:
  "rank_index (mirror_rank r) < rank_index (mirror_rank s) \<longleftrightarrow>
    rank_index s < rank_index r"
  by (cases r; cases s; simp add: rank_index_def)

lemma int_rank_index_mirror_less:
  "int (rank_index (mirror_rank r)) <
      int (rank_index (mirror_rank s)) \<longleftrightarrow>
    int (rank_index s) < int (rank_index r)"
  by (cases r; cases s; simp add: rank_index_def)

lemma mirror_square_involutive:
  "mirror_square (mirror_square s) = s"
  by (cases s; simp add: mirror_square_def mirror_rank_involutive)

lemma mirror_square_eq_iff:
  "mirror_square s = mirror_square t \<longleftrightarrow> s = t"
proof
  assume h: "mirror_square s = mirror_square t"
  have "mirror_square (mirror_square s) =
      mirror_square (mirror_square t)"
    using h by simp
  then show "s = t"
    by (simp add: mirror_square_involutive)
next
  assume "s = t"
  then show "mirror_square s = mirror_square t" by simp
qed

lemma mirror_square_in_set_all_squares:
  "mirror_square s \<in> set all_squares \<longleftrightarrow> s \<in> set all_squares"
  by (cases s; simp add: all_squares_set mirror_square_def)

lemma same_file_mirror:
  "same_file (mirror_square s) (mirror_square t) \<longleftrightarrow>
     same_file s t"
  by (cases s; cases t; simp add: same_file_def mirror_square_def)

lemma same_rank_mirror:
  "same_rank (mirror_square s) (mirror_square t) \<longleftrightarrow>
     same_rank s t"
  by (cases s; cases t; simp add: same_rank_def mirror_square_def
      mirror_rank_eq_iff)

lemma same_diagonal_mirror:
  "same_diagonal (mirror_square s) (mirror_square t) \<longleftrightarrow>
     same_diagonal s t"
  by (cases s; cases t; simp add: same_diagonal_def mirror_square_def
      rank_index_mirror int_rank_index_mirror_diff disj_commute)

lemma rook_geometry_mirror:
  "rook_geometry (mirror_square s) (mirror_square t) \<longleftrightarrow>
     rook_geometry s t"
  by (simp add: rook_geometry_def same_file_mirror same_rank_mirror
      mirror_square_eq_iff)

lemma bishop_geometry_mirror:
  "bishop_geometry (mirror_square s) (mirror_square t) \<longleftrightarrow>
     bishop_geometry s t"
  by (simp add: bishop_geometry_def same_diagonal_mirror
      mirror_square_eq_iff)

lemma queen_geometry_mirror:
  "queen_geometry (mirror_square s) (mirror_square t) \<longleftrightarrow>
     queen_geometry s t"
  by (simp add: queen_geometry_def rook_geometry_mirror
      bishop_geometry_mirror)

lemma knight_geometry_mirror:
  "knight_geometry (mirror_square s) (mirror_square t) \<longleftrightarrow>
     knight_geometry s t"
  by (cases s; cases t; simp add: knight_geometry_def mirror_square_def
      rank_index_mirror abs_int_rank_index_mirror_diff)

lemma king_geometry_mirror:
  "king_geometry (mirror_square s) (mirror_square t) \<longleftrightarrow>
     king_geometry s t"
  by (cases s; cases t; simp add: king_geometry_def mirror_square_def
      rank_index_mirror abs_int_rank_index_mirror_diff)

lemma pawn_move_geometry_mirror:
  "pawn_move_geometry (opponent c) (mirror_square s) (mirror_square t) \<longleftrightarrow>
     pawn_move_geometry c s t"
  by (cases c; cases s; cases t;
      simp add: pawn_move_geometry_def mirror_square_def rank_index_mirror
        nat_rank_index_mirror_suc)

lemma pawn_attack_geometry_mirror:
  "pawn_attack_geometry (opponent c) (mirror_square s) (mirror_square t) \<longleftrightarrow>
     pawn_attack_geometry c s t"
  by (cases c; cases s; cases t;
      simp add: pawn_attack_geometry_def mirror_square_def rank_index_mirror
        nat_rank_index_mirror_suc)

lemma pawn_attack_geometry_mirror_eq:
  "pawn_attack_geometry (opponent c) (mirror_square s) (mirror_square t) =
     pawn_attack_geometry c s t"
  by (cases c; cases s; cases t;
      simp add: pawn_attack_geometry_def mirror_square_def rank_index_mirror
        nat_rank_index_mirror_suc)

lemma pawn_attack_geometry_mirror_white:
  "pawn_attack_geometry Black (mirror_square s) (mirror_square t) =
     pawn_attack_geometry White s t"
  by (cases s; cases t;
      simp add: pawn_attack_geometry_def mirror_square_def rank_index_mirror
        nat_rank_index_mirror_suc)

lemma pawn_attack_geometry_mirror_black:
  "pawn_attack_geometry White (mirror_square s) (mirror_square t) =
     pawn_attack_geometry Black s t"
  by (cases s; cases t;
      simp add: pawn_attack_geometry_def mirror_square_def rank_index_mirror
        nat_rank_index_mirror_suc)

lemma pawn_double_geometry_mirror:
  "pawn_double_geometry (opponent c) (mirror_square s) (mirror_square t) \<longleftrightarrow>
     pawn_double_geometry c s t"
proof -
  obtain sf sr where hs: "s = (sf,sr)" by (cases s) simp
  obtain tf tr where ht: "t = (tf,tr)" by (cases t) simp
  show ?thesis
    using hs ht
    by (cases c; cases sr; cases tr;
        simp add: pawn_double_geometry_def mirror_square_def)
qed

lemma promotion_rank_mirror:
  "promotion_rank (opponent c) = mirror_rank (promotion_rank c)"
  by (cases c; simp add: promotion_rank_def)

lemma mirror_square_rank_less:
  "rank_index (snd (mirror_square s)) < rank_index (snd (mirror_square t))
    \<longleftrightarrow> rank_index (snd t) < rank_index (snd s)"
  by (cases s; cases t; simp add: mirror_square_def rank_index_mirror_less)

lemma mirror_square_file_index:
  "file_index (fst (mirror_square s)) = file_index (fst s)"
  by (cases s; simp add: mirror_square_def)

lemma between_mirror:
  "between (mirror_square s) (mirror_square u) (mirror_square t) \<longleftrightarrow>
     between s u t"
  by (simp add: between_def mirror_square_eq_iff same_file_mirror same_rank_mirror
      same_diagonal_mirror mirror_square_rank_less mirror_square_file_index
      disj_commute conj_commute)

lemma between_mirror_middle:
  "between (mirror_square s) u (mirror_square t) \<longleftrightarrow>
     between s (mirror_square u) t"
proof -
  have h:
      "between (mirror_square s) (mirror_square (mirror_square u))
          (mirror_square t) \<longleftrightarrow>
        between s (mirror_square u) t"
    by (rule between_mirror)
  show ?thesis
    using h by (simp add: mirror_square_involutive)
qed

lemma clear_between_mirror:
  "clear_between (mirror_board b) (mirror_square s) (mirror_square t) \<longleftrightarrow>
     clear_between b s t"
proof (unfold clear_between_def; rule iffI)
  assume hclear:
    "\<forall>u\<in>set (squares_between (mirror_square s) (mirror_square t)).
      mirror_board b u = None"
  show "\<forall>u\<in>set (squares_between s t). b u = None"
  proof
    fix u
    assume hu: "u \<in> set (squares_between s t)"
    have hum: "mirror_square u \<in>
        set (squares_between (mirror_square s) (mirror_square t))"
      using hu by (simp add: squares_between_correct between_mirror
          mirror_square_in_set_all_squares)
    have hboard: "mirror_board b (mirror_square u) = None"
      using hclear hum by blast
    show "b u = None"
      using hboard
      by (cases "b u"; simp add: mirror_board_def mirror_square_involutive
          mirror_piece_def split: option.splits)
  qed
next
  assume hclear:
    "\<forall>u\<in>set (squares_between s t). b u = None"
  show "\<forall>u\<in>set (squares_between (mirror_square s) (mirror_square t)).
      mirror_board b u = None"
  proof
    fix u
    assume hu: "u \<in> set (squares_between (mirror_square s) (mirror_square t))"
    have hum: "mirror_square u \<in> set (squares_between s t)"
      using hu by (simp add: squares_between_correct between_mirror_middle
          mirror_square_in_set_all_squares)
    have hboard: "b (mirror_square u) = None"
      using hclear hum by blast
    show "mirror_board b u = None"
      using hboard
      by (simp add: mirror_board_def mirror_square_involutive
          split: option.splits)
  qed
qed

lemma mirror_piece_involutive:
  "mirror_piece (mirror_piece q) = q"
  by (cases q; simp_all add: mirror_piece_def opponent_involutive)

lemma mirror_move_involutive:
  "mirror_move (mirror_move m) = m"
  by (cases m; simp add: mirror_square_involutive)

lemma mirror_board_update:
  "mirror_board (board_update b s x) (mirror_square t) =
    (if t = s then
       (case x of None \<Rightarrow> None | Some q \<Rightarrow> Some (mirror_piece q))
     else mirror_board b (mirror_square t))"
  by (simp add: mirror_board_def board_update_def mirror_square_involutive
      split: option.splits)

lemma mirror_board_lookup:
  "mirror_board b (mirror_square s) =
     map_option mirror_piece (b s)"
  by (simp add: mirror_board_def mirror_square_involutive
      split: option.splits)

lemma slider_attack_mirror:
  "slider_attack (mirror_position p) (mirror_square s) (mirror_square t) \<longleftrightarrow>
     slider_attack p s t"
  by (simp add: slider_attack_def mirror_position_def clear_between_mirror)

lemma mirror_position_board_lookup:
  "position_board (mirror_position p) (mirror_square s) =
     map_option mirror_piece (position_board p s)"
  by (simp add: mirror_position_def mirror_board_lookup)

lemma piece_attacks_mirror:
  "piece_attacks (mirror_position p) (opponent c)
      (mirror_square s) (mirror_square t) \<longleftrightarrow>
     piece_attacks p c s t"
proof (cases "position_board p s")
  case None
  then show ?thesis
    by (simp add: piece_attacks_def mirror_position_board_lookup)
next
  case (Some q)
  obtain c' k' where hq: "q = \<lparr>piece_color = c', piece_kind = k'\<rparr>"
    by (cases q; simp)
  then show ?thesis
    using Some by (cases c; cases c'; cases k';
      simp add: piece_attacks_def mirror_position_board_lookup
        mirror_piece_def slider_attack_mirror rook_geometry_mirror
        bishop_geometry_mirror queen_geometry_mirror knight_geometry_mirror
        king_geometry_mirror pawn_attack_geometry_mirror_eq
        pawn_attack_geometry_mirror_white pawn_attack_geometry_mirror_black
        opponent_involutive)
qed

lemma is_attacked_mirror:
  "is_attacked (mirror_position p) (opponent c) (mirror_square t) \<longleftrightarrow>
     is_attacked p c t"
proof (rule iffI)
  assume h:
    "is_attacked (mirror_position p) (opponent c) (mirror_square t)"
  have hiff:
      "is_attacked (mirror_position p) (opponent c) (mirror_square t) \<longleftrightarrow>
        (\<exists>u. piece_attacks (mirror_position p) (opponent c)
          u (mirror_square t))"
    by (rule is_attacked_iff)
  obtain u where hu:
      "piece_attacks (mirror_position p) (opponent c) u (mirror_square t)"
    using h hiff by blast
  have hpm:
      "piece_attacks (mirror_position p) (opponent c)
          (mirror_square (mirror_square u)) (mirror_square t) \<longleftrightarrow>
        piece_attacks p c (mirror_square u) t"
    by (rule piece_attacks_mirror)
  have hp: "piece_attacks p c (mirror_square u) t"
    using hu hpm by (simp add: mirror_square_involutive)
  show "is_attacked p c t"
  proof (rule iffD2[OF is_attacked_iff])
    show "\<exists>u. piece_attacks p c u t"
      using hp by blast
  qed
next
  assume h: "is_attacked p c t"
  have hiff:
      "is_attacked p c t \<longleftrightarrow> (\<exists>u. piece_attacks p c u t)"
    by (rule is_attacked_iff)
  obtain u where hu: "piece_attacks p c u t"
    using h hiff by blast
  have hp:
      "piece_attacks (mirror_position p) (opponent c)
        (mirror_square u) (mirror_square t)"
    using hu by (simp add: piece_attacks_mirror)
  show "is_attacked (mirror_position p) (opponent c) (mirror_square t)"
  proof (rule iffD2[OF is_attacked_iff])
    show "\<exists>u. piece_attacks (mirror_position p) (opponent c)
      u (mirror_square t)"
      using hp by blast
  qed
qed

lemma has_piece_mirror:
  "has_piece (mirror_board b) (mirror_square s) (opponent c) k \<longleftrightarrow>
     has_piece b s c k"
proof (cases "b s")
  case None
  then show ?thesis
    by (simp add: has_piece_def mirror_board_lookup)
next
  case (Some q)
  obtain c0 k0 where hq: "q = \<lparr>piece_color = c0, piece_kind = k0\<rparr>"
    by (cases q; simp)
  then show ?thesis
    using Some by (cases c; cases c0; cases k0;
      simp add: has_piece_def mirror_board_lookup mirror_piece_def
        opponent_involutive)
qed

lemma king_square_mirror_unique:
  assumes hex:
      "\<exists>s \<in> set all_squares. has_piece b s c King"
    and hunique:
      "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
        has_piece b s c King \<longrightarrow>
        has_piece b t c King \<longrightarrow> s = t"
  shows
    "king_square (mirror_board b) (opponent c) =
      map_option mirror_square (king_square b c)"
proof -
  obtain s0 where hs0set: "s0 \<in> set all_squares"
    and hs0piece: "has_piece b s0 c King"
    using hex by blast
  have hknone: "king_square b c \<noteq> None"
    using hs0set hs0piece
    by (simp add: king_square_none_iff; blast)
  obtain s where hks: "king_square b c = Some s"
    using hknone by (cases "king_square b c"; simp)
  have hsset: "s \<in> set all_squares"
    using king_square_some[OF hks] by simp
  have hspiece: "has_piece b s c King"
    using king_square_some[OF hks] by simp
  have hmsset: "mirror_square s \<in> set all_squares"
    using hsset by (simp add: mirror_square_in_set_all_squares)
  have hmpiece:
      "has_piece (mirror_board b) (mirror_square s) (opponent c) King"
    using has_piece_mirror[of b s c King] hspiece by blast
  have hmnone:
      "king_square (mirror_board b) (opponent c) \<noteq> None"
    using hmsset hmpiece
    by (simp add: king_square_none_iff; blast)
  obtain t where hkt:
      "king_square (mirror_board b) (opponent c) = Some t"
    using hmnone
    by (cases "king_square (mirror_board b) (opponent c)"; simp)
  have htset: "t \<in> set all_squares"
    using king_square_some[OF hkt] by simp
  have htpiece:
      "has_piece (mirror_board b) t (opponent c) King"
    using king_square_some[OF hkt] by simp
  have htmset: "mirror_square t \<in> set all_squares"
    using htset by (simp add: mirror_square_in_set_all_squares)
  have htpiece_orig: "has_piece b (mirror_square t) c King"
    using has_piece_mirror[of b "mirror_square t" c King] htpiece
    by (simp add: mirror_square_involutive)
  have hts: "mirror_square t = s"
    using hunique hspiece htpiece_orig hsset htmset by blast
  have hts': "t = mirror_square s"
    using hts by (metis mirror_square_involutive)
  show ?thesis
    using hks hkt hts' by simp
qed

lemma in_check_mirror_unique:
  assumes hex:
      "\<exists>s \<in> set all_squares.
        has_piece (position_board p) s c King"
    and hunique:
      "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
        has_piece (position_board p) s c King \<longrightarrow>
        has_piece (position_board p) t c King \<longrightarrow> s = t"
  shows
    "in_check (mirror_position p) (opponent c) \<longleftrightarrow>
      in_check p c"
proof -
  have hk:
      "king_square (position_board (mirror_position p)) (opponent c) =
        map_option mirror_square (king_square (position_board p) c)"
    using king_square_mirror_unique[of "position_board p" c] hex hunique
    by (simp add: mirror_position_def)
  have hknone:
      "king_square (position_board p) c \<noteq> None"
    using hex by (simp add: king_square_none_iff; blast)
  obtain s where hks:
      "king_square (position_board p) c = Some s"
    using hknone
    by (cases "king_square (position_board p) c"; simp)
  have hkm:
      "king_square (position_board (mirror_position p)) (opponent c) =
        Some (mirror_square s)"
    using hk hks by simp
  have hatt0:
      "is_attacked (mirror_position p) (opponent (opponent c))
          (mirror_square s) \<longleftrightarrow>
        is_attacked p (opponent c) s"
    by (rule is_attacked_mirror)
  have hatt:
      "is_attacked (mirror_position p) c (mirror_square s) \<longleftrightarrow>
        is_attacked p (opponent c) s"
    using hatt0 by (simp add: opponent_involutive)
  show ?thesis
    unfolding in_check_def
    using hks hkm hatt by (simp add: opponent_involutive)
qed

lemma destination_friendly_mirror:
  "destination_friendly (mirror_position p) (opponent c) (mirror_square t) \<longleftrightarrow>
     destination_friendly p c t"
proof (cases "position_board p t")
  case None
  then show ?thesis
    by (simp add: destination_friendly_def mirror_position_board_lookup)
next
  case (Some q)
  obtain c' k' where hq: "q = \<lparr>piece_color = c', piece_kind = k'\<rparr>"
    by (cases q; simp)
  then show ?thesis
    using Some by (cases c; cases c'; cases k';
      simp add: destination_friendly_def mirror_position_board_lookup
        mirror_piece_def opponent_involutive)
qed

lemma mirror_board_involutive:
  "mirror_board (mirror_board b) = b"
proof (rule ext)
  fix s
  show "mirror_board (mirror_board b) s = b s"
    by (simp add: mirror_board_def mirror_square_involutive mirror_piece_involutive
        split: option.splits)
qed

lemma mirror_right_involutive:
  "mirror_right (mirror_right r) = r"
  by (cases r; simp)

lemma mirror_rights_involutive:
  "mirror_rights (mirror_rights R) = R"
  by (simp add: mirror_rights_def image_image mirror_right_involutive)

lemma map_option_mirror_square_involutive:
  "map_option mirror_square (map_option mirror_square x) = x"
  by (cases x; simp add: mirror_square_involutive)

lemma mirror_position_involutive:
  "mirror_position (mirror_position p) = p"
  by (cases p; simp add: mirror_position_def mirror_board_involutive
      mirror_rights_involutive map_option_mirror_square_involutive
      mirror_square_involutive opponent_involutive)

lemma opponent_eq_opponent_iff:
  "opponent a = opponent b \<longleftrightarrow> a = b"
  by (cases a; cases b; simp)

lemma opponent_eq_iff:
  "opponent a = b \<longleftrightarrow> a = opponent b"
  by (cases a; cases b; simp)

lemma mirror_position_board_none:
  "position_board (mirror_position p) (mirror_square t) = None \<longleftrightarrow>
     position_board p t = None"
  by (cases "position_board p t";
      simp add: mirror_position_board_lookup mirror_piece_def)

lemma mirror_position_board_color:
  "(case position_board (mirror_position p) (mirror_square t) of
      None \<Rightarrow> False | Some q \<Rightarrow> piece_color q = opponent c) \<longleftrightarrow>
     (case position_board p t of
      None \<Rightarrow> False | Some q \<Rightarrow> piece_color q = c)"
  by (cases "position_board p t";
      simp add: mirror_position_board_lookup mirror_piece_def
        opponent_involutive opponent_eq_opponent_iff)

lemma clear_between_position_mirror:
  "clear_between (position_board (mirror_position p))
      (mirror_square s) (mirror_square t) \<longleftrightarrow>
     clear_between (position_board p) s t"
  by (simp add: mirror_position_def clear_between_mirror)

lemma normal_piece_geometry_mirror:
  "normal_piece_geometry (mirror_position p) (opponent c) (mirror_piece q)
      (mirror_square s) (mirror_square t) \<longleftrightarrow>
     normal_piece_geometry p c q s t"
  by (cases q; cases "piece_kind q";
      simp add: normal_piece_geometry_def
        mirror_position_board_lookup mirror_position_board_none
        mirror_position_board_color mirror_piece_def
        rook_geometry_mirror bishop_geometry_mirror queen_geometry_mirror
        knight_geometry_mirror king_geometry_mirror
        pawn_move_geometry_mirror pawn_double_geometry_mirror
        pawn_attack_geometry_mirror clear_between_position_mirror
        opponent_involutive opponent_eq_iff split: option.splits)

lemma move_source_mirror:
  "move_source (mirror_move m) = mirror_square (move_source m)"
  by (cases m; simp add: mirror_square_def)

lemma move_destination_mirror:
  "move_destination (mirror_move m) = mirror_square (move_destination m)"
  by (cases m; simp add: mirror_square_def)

lemma snd_mirror_square:
  "snd (mirror_square s) = mirror_rank (snd s)"
  by (cases s; simp add: mirror_square_def)

lemma castle_right_of_mirror:
  "castle_right_of (mirror_move m) =
     map_option mirror_right (castle_right_of m)"
  by (cases m; simp)

lemma castle_color_of_mirror:
  "castle_color_of (mirror_move m) =
     map_option opponent (castle_color_of m)"
  by (cases m; simp)

lemma castle_rook_source_mirror:
  "castle_rook_source (mirror_move m) =
     map_option mirror_square (castle_rook_source m)"
  by (cases m; simp add: mirror_square_def)

lemma castle_rook_destination_mirror:
  "castle_rook_destination (mirror_move m) =
     map_option mirror_square (castle_rook_destination m)"
  by (cases m; simp add: mirror_square_def)

lemma castle_transit_square_mirror:
  "castle_transit_square (mirror_move m) =
     map_option mirror_square (castle_transit_square m)"
  by (cases m; simp add: mirror_square_def)

lemma castle_empty_squares_mirror:
  "set (castle_empty_squares (mirror_move m)) =
     mirror_square ` set (castle_empty_squares m)"
  by (cases m; simp add: castle_empty_squares_def mirror_square_def)

lemma castle_clear_mirror:
  "castle_clear (mirror_position p) (mirror_move m) \<longleftrightarrow>
     castle_clear p m"
proof (unfold castle_clear_def; rule iffI)
  assume hclear:
    "\<forall>s\<in>set (castle_empty_squares (mirror_move m)).
      position_board (mirror_position p) s = None"
  show "\<forall>s\<in>set (castle_empty_squares m).
      position_board p s = None"
  proof
    fix s
    assume hs: "s \<in> set (castle_empty_squares m)"
    have hsm:
        "mirror_square s \<in> set (castle_empty_squares (mirror_move m))"
      using hs by (simp add: castle_empty_squares_mirror)
    have hb:
        "position_board (mirror_position p) (mirror_square s) = None"
      using hclear hsm by blast
    show "position_board p s = None"
      using hb by (simp add: mirror_position_board_none)
  qed
next
  assume hclear:
    "\<forall>s\<in>set (castle_empty_squares m). position_board p s = None"
  show "\<forall>s\<in>set (castle_empty_squares (mirror_move m)).
      position_board (mirror_position p) s = None"
  proof
    fix s
    assume hs: "s \<in> set (castle_empty_squares (mirror_move m))"
    obtain u where hu: "u \<in> set (castle_empty_squares m)"
      and hsu: "s = mirror_square u"
      using hs by (auto simp add: castle_empty_squares_mirror)
    have hb: "position_board p u = None"
      using hclear hu by blast
    show "position_board (mirror_position p) s = None"
      using hb hsu by (simp add: mirror_position_board_none)
  qed
qed

lemma mirror_right_member:
  "mirror_right r \<in> mirror_rights R \<longleftrightarrow> r \<in> R"
proof
  assume h: "mirror_right r \<in> mirror_rights R"
  obtain x where hx: "x \<in> R" and hxr: "mirror_right x = mirror_right r"
    using h by (auto simp add: mirror_rights_def)
  have "x = r"
    using hxr by (metis mirror_right_involutive)
  then show "r \<in> R" using hx by simp
next
  assume h: "r \<in> R"
  show "mirror_right r \<in> mirror_rights R"
    using h by (simp add: mirror_rights_def)
qed

lemma has_piece_position_mirror:
  "has_piece (position_board (mirror_position p)) (mirror_square s)
      (opponent c) k \<longleftrightarrow>
     has_piece (position_board p) s c k"
  by (simp add: mirror_position_def has_piece_mirror)

lemma has_piece_position_mirror_opponent:
  "has_piece (position_board (mirror_position p)) (mirror_square s) c k
      \<longleftrightarrow>
     has_piece (position_board p) s (opponent c) k"
proof (cases c)
  case White
  have h:
      "has_piece (position_board (mirror_position p)) (mirror_square s)
        (opponent Black) k \<longleftrightarrow>
       has_piece (position_board p) s Black k"
    by (rule has_piece_position_mirror)
  then show ?thesis by (simp add: White)
next
  case Black
  have h:
      "has_piece (position_board (mirror_position p)) (mirror_square s)
        (opponent White) k \<longleftrightarrow>
       has_piece (position_board p) s White k"
    by (rule has_piece_position_mirror)
  then show ?thesis by (simp add: Black)
qed

lemma position_turn_mirror:
  "position_turn (mirror_position p) = opponent (position_turn p)"
  by (simp add: mirror_position_def)

lemma position_castling_mirror:
  "position_castling (mirror_position p) = mirror_rights (position_castling p)"
  by (simp add: mirror_position_def)

lemma has_piece_mirror_rank1:
  "has_piece (position_board (mirror_position p)) (f, R8) (opponent c) k
      \<longleftrightarrow>
     has_piece (position_board p) (f, R1) c k"
proof -
  have h:
      "has_piece (position_board (mirror_position p))
        (mirror_square (f, R1)) (opponent c) k \<longleftrightarrow>
       has_piece (position_board p) (f, R1) c k"
    by (rule has_piece_position_mirror)
  then show ?thesis by (simp add: mirror_square_def)
qed

lemma has_piece_mirror_rank8:
  "has_piece (position_board (mirror_position p)) (f, R1) (opponent c) k
      \<longleftrightarrow>
     has_piece (position_board p) (f, R8) c k"
proof -
  have h:
      "has_piece (position_board (mirror_position p))
        (mirror_square (f, R8)) (opponent c) k \<longleftrightarrow>
       has_piece (position_board p) (f, R8) c k"
    by (rule has_piece_position_mirror)
  then show ?thesis by (simp add: mirror_square_def)
qed

lemma is_attacked_mirror_rank1:
  "is_attacked (mirror_position p) (opponent c) (f,R8)
      \<longleftrightarrow> is_attacked p c (f,R1)"
proof -
  have h:
      "is_attacked (mirror_position p) (opponent c)
        (mirror_square (f,R1)) \<longleftrightarrow>
       is_attacked p c (f,R1)"
    by (rule is_attacked_mirror)
  then show ?thesis by (simp add: mirror_square_def)
qed

lemma is_attacked_mirror_rank8:
  "is_attacked (mirror_position p) (opponent c) (f,R1)
      \<longleftrightarrow> is_attacked p c (f,R8)"
proof -
  have h:
      "is_attacked (mirror_position p) (opponent c)
        (mirror_square (f,R8)) \<longleftrightarrow>
       is_attacked p c (f,R8)"
    by (rule is_attacked_mirror)
  then show ?thesis by (simp add: mirror_square_def)
qed

lemma pseudo_legal_castle_mirror:
  "pseudo_legal_castle (mirror_position p) (mirror_move m) \<longleftrightarrow>
     pseudo_legal_castle p m"
proof (cases m)
  case (Normal s t)
  then show ?thesis by (simp add: pseudo_legal_castle_def)
next
  case (Promotion s t k)
  then show ?thesis by (simp add: pseudo_legal_castle_def)
next
  case (EnPassant s t)
  then show ?thesis by (simp add: pseudo_legal_castle_def)
next
  case WhiteKingCastle
  have ht:
      "opponent (position_turn p) = Black \<longleftrightarrow>
       position_turn p = White"
    by (cases "position_turn p"; simp)
  have hr:
      "BlackKingSide \<in> mirror_rights (position_castling p) \<longleftrightarrow>
       WhiteKingSide \<in> position_castling p"
    using mirror_right_member[of WhiteKingSide "position_castling p"]
    by simp
  have hk:
      "has_piece (position_board (mirror_position p)) (E,R8) Black King
        \<longleftrightarrow>
       has_piece (position_board p) (E,R1) White King"
    using has_piece_mirror_rank1[of p E White King] by simp
  have hro:
      "has_piece (position_board (mirror_position p)) (H,R8) Black Rook
        \<longleftrightarrow>
       has_piece (position_board p) (H,R1) White Rook"
    using has_piece_mirror_rank1[of p H White Rook] by simp
  have hc:
      "castle_clear (mirror_position p) BlackKingCastle
        \<longleftrightarrow> castle_clear p WhiteKingCastle"
    using castle_clear_mirror[of p WhiteKingCastle] by simp
  have hgoal:
      "pseudo_legal_castle (mirror_position p) BlackKingCastle
        \<longleftrightarrow> pseudo_legal_castle p WhiteKingCastle"
    by (simp add: pseudo_legal_castle_def position_turn_mirror
        position_castling_mirror ht hr hk hro hc)
  then show ?thesis using WhiteKingCastle by simp
next
  case WhiteQueenCastle
  have ht:
      "opponent (position_turn p) = Black \<longleftrightarrow>
       position_turn p = White"
    by (cases "position_turn p"; simp)
  have hr:
      "BlackQueenSide \<in> mirror_rights (position_castling p) \<longleftrightarrow>
       WhiteQueenSide \<in> position_castling p"
    using mirror_right_member[of WhiteQueenSide "position_castling p"]
    by simp
  have hk:
      "has_piece (position_board (mirror_position p)) (E,R8) Black King
        \<longleftrightarrow>
       has_piece (position_board p) (E,R1) White King"
    using has_piece_mirror_rank1[of p E White King] by simp
  have hro:
      "has_piece (position_board (mirror_position p)) (A,R8) Black Rook
        \<longleftrightarrow>
       has_piece (position_board p) (A,R1) White Rook"
    using has_piece_mirror_rank1[of p A White Rook] by simp
  have hc:
      "castle_clear (mirror_position p) BlackQueenCastle
        \<longleftrightarrow> castle_clear p WhiteQueenCastle"
    using castle_clear_mirror[of p WhiteQueenCastle] by simp
  have hgoal:
      "pseudo_legal_castle (mirror_position p) BlackQueenCastle
        \<longleftrightarrow> pseudo_legal_castle p WhiteQueenCastle"
    by (simp add: pseudo_legal_castle_def position_turn_mirror
        position_castling_mirror ht hr hk hro hc)
  then show ?thesis using WhiteQueenCastle by simp
next
  case BlackKingCastle
  have ht:
      "opponent (position_turn p) = White \<longleftrightarrow>
       position_turn p = Black"
    by (cases "position_turn p"; simp)
  have hr:
      "WhiteKingSide \<in> mirror_rights (position_castling p) \<longleftrightarrow>
       BlackKingSide \<in> position_castling p"
    using mirror_right_member[of BlackKingSide "position_castling p"]
    by simp
  have hk:
      "has_piece (position_board (mirror_position p)) (E,R1) White King
        \<longleftrightarrow>
       has_piece (position_board p) (E,R8) Black King"
    using has_piece_mirror_rank8[of p E Black King] by simp
  have hro:
      "has_piece (position_board (mirror_position p)) (H,R1) White Rook
        \<longleftrightarrow>
       has_piece (position_board p) (H,R8) Black Rook"
    using has_piece_mirror_rank8[of p H Black Rook] by simp
  have hc:
      "castle_clear (mirror_position p) WhiteKingCastle
        \<longleftrightarrow> castle_clear p BlackKingCastle"
    using castle_clear_mirror[of p BlackKingCastle] by simp
  have hgoal:
      "pseudo_legal_castle (mirror_position p) WhiteKingCastle
        \<longleftrightarrow> pseudo_legal_castle p BlackKingCastle"
    by (simp add: pseudo_legal_castle_def position_turn_mirror
        position_castling_mirror ht hr hk hro hc)
  then show ?thesis using BlackKingCastle by simp
next
  case BlackQueenCastle
  have ht:
      "opponent (position_turn p) = White \<longleftrightarrow>
       position_turn p = Black"
    by (cases "position_turn p"; simp)
  have hr:
      "WhiteQueenSide \<in> mirror_rights (position_castling p) \<longleftrightarrow>
       BlackQueenSide \<in> position_castling p"
    using mirror_right_member[of BlackQueenSide "position_castling p"]
    by simp
  have hk:
      "has_piece (position_board (mirror_position p)) (E,R1) White King
        \<longleftrightarrow>
       has_piece (position_board p) (E,R8) Black King"
    using has_piece_mirror_rank8[of p E Black King] by simp
  have hro:
      "has_piece (position_board (mirror_position p)) (A,R1) White Rook
        \<longleftrightarrow>
       has_piece (position_board p) (A,R8) Black Rook"
    using has_piece_mirror_rank8[of p A Black Rook] by simp
  have hc:
      "castle_clear (mirror_position p) WhiteQueenCastle
        \<longleftrightarrow> castle_clear p BlackQueenCastle"
    using castle_clear_mirror[of p BlackQueenCastle] by simp
  have hgoal:
      "pseudo_legal_castle (mirror_position p) WhiteQueenCastle
        \<longleftrightarrow> pseudo_legal_castle p BlackQueenCastle"
    by (simp add: pseudo_legal_castle_def position_turn_mirror
        position_castling_mirror ht hr hk hro hc)
  then show ?thesis using BlackQueenCastle by simp
qed

lemma castle_safe_squares_mirror:
  "castle_safe_squares (mirror_position p) (mirror_move m) \<longleftrightarrow>
     castle_safe_squares p m"
proof (cases m)
  case (Normal s t)
  then show ?thesis by (simp add: castle_safe_squares_def)
next
  case (Promotion s t k)
  then show ?thesis by (simp add: castle_safe_squares_def)
next
  case (EnPassant s t)
  then show ?thesis by (simp add: castle_safe_squares_def)
next
  case WhiteKingCastle
  have hE:
      "\<not> is_attacked (mirror_position p) White (E,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (E,R1)"
    using is_attacked_mirror_rank1[of p Black E] by simp
  have hF:
      "\<not> is_attacked (mirror_position p) White (F,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (F,R1)"
    using is_attacked_mirror_rank1[of p Black F] by simp
  have hG:
      "\<not> is_attacked (mirror_position p) White (G,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (G,R1)"
    using is_attacked_mirror_rank1[of p Black G] by simp
  have hgoal:
      "castle_safe_squares (mirror_position p) BlackKingCastle
        \<longleftrightarrow> castle_safe_squares p WhiteKingCastle"
    by (simp add: castle_safe_squares_def hE hF hG)
  then show ?thesis using WhiteKingCastle by simp
next
  case WhiteQueenCastle
  have hE:
      "\<not> is_attacked (mirror_position p) White (E,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (E,R1)"
    using is_attacked_mirror_rank1[of p Black E] by simp
  have hD:
      "\<not> is_attacked (mirror_position p) White (D,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (D,R1)"
    using is_attacked_mirror_rank1[of p Black D] by simp
  have hC:
      "\<not> is_attacked (mirror_position p) White (C,R8) \<longleftrightarrow>
       \<not> is_attacked p Black (C,R1)"
    using is_attacked_mirror_rank1[of p Black C] by simp
  have hgoal:
      "castle_safe_squares (mirror_position p) BlackQueenCastle
        \<longleftrightarrow> castle_safe_squares p WhiteQueenCastle"
    by (simp add: castle_safe_squares_def hE hD hC)
  then show ?thesis using WhiteQueenCastle by simp
next
  case BlackKingCastle
  have hE:
      "\<not> is_attacked (mirror_position p) Black (E,R1) \<longleftrightarrow>
       \<not> is_attacked p White (E,R8)"
    using is_attacked_mirror_rank8[of p White E] by simp
  have hF:
      "\<not> is_attacked (mirror_position p) Black (F,R1) \<longleftrightarrow>
       \<not> is_attacked p White (F,R8)"
    using is_attacked_mirror_rank8[of p White F] by simp
  have hG:
      "\<not> is_attacked (mirror_position p) Black (G,R1) \<longleftrightarrow>
       \<not> is_attacked p White (G,R8)"
    using is_attacked_mirror_rank8[of p White G] by simp
  have hgoal:
      "castle_safe_squares (mirror_position p) WhiteKingCastle
        \<longleftrightarrow> castle_safe_squares p BlackKingCastle"
    by (simp add: castle_safe_squares_def hE hF hG)
  then show ?thesis using BlackKingCastle by simp
next
  case BlackQueenCastle
  have hE:
      "\<not> is_attacked (mirror_position p) Black (E,R1) \<longleftrightarrow>
       \<not> is_attacked p White (E,R8)"
    using is_attacked_mirror_rank8[of p White E] by simp
  have hD:
      "\<not> is_attacked (mirror_position p) Black (D,R1) \<longleftrightarrow>
       \<not> is_attacked p White (D,R8)"
    using is_attacked_mirror_rank8[of p White D] by simp
  have hC:
      "\<not> is_attacked (mirror_position p) Black (C,R1) \<longleftrightarrow>
       \<not> is_attacked p White (C,R8)"
    using is_attacked_mirror_rank8[of p White C] by simp
  have hgoal:
      "castle_safe_squares (mirror_position p) WhiteQueenCastle
        \<longleftrightarrow> castle_safe_squares p BlackQueenCastle"
    by (simp add: castle_safe_squares_def hE hD hC)
  then show ?thesis using BlackQueenCastle by simp
qed

lemma pseudo_legal_promotion_mirror:
  "pseudo_legal_promotion (mirror_position p) (mirror_move m)
      \<longleftrightarrow> pseudo_legal_promotion p m"
proof (cases m)
  case (Normal s t)
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
next
  case (Promotion s t k)
  then show ?thesis
    by (cases "position_board p s"; cases "position_board p t";
        simp add: pseudo_legal_promotion_def
          mirror_position_board_lookup mirror_position_board_none
          mirror_position_board_color mirror_piece_def promotion_rank_mirror
          pawn_move_geometry_mirror pawn_attack_geometry_mirror
          position_turn_mirror opponent_involutive opponent_eq_iff
          snd_mirror_square mirror_rank_eq_iff Promotion split: option.splits)
next
  case (EnPassant s t)
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
next
  case WhiteKingCastle
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
next
  case WhiteQueenCastle
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
next
  case BlackKingCastle
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
next
  case BlackQueenCastle
  then show ?thesis by (simp add: pseudo_legal_promotion_def)
qed

lemma ep_captured_square_mirror:
  "ep_captured_square (opponent c) (mirror_square t) =
     map_option mirror_square (ep_captured_square c t)"
proof -
  obtain tf tr where ht: "t = (tf,tr)" by (cases t) simp
  show ?thesis using ht
    by (cases c; cases tr; simp add: ep_captured_square_def mirror_square_def)
qed

lemma position_en_passant_mirror:
  "position_en_passant (mirror_position p) =
     map_option mirror_square (position_en_passant p)"
  by (simp add: mirror_position_def)

lemma pseudo_legal_en_passant_mirror:
  "pseudo_legal_en_passant (mirror_position p) (mirror_move m)
      \<longleftrightarrow> pseudo_legal_en_passant p m"
proof (cases m)
  case (Normal s t)
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
next
  case (Promotion s t k)
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
next
  case (EnPassant s t)
  then show ?thesis
    by (simp add: pseudo_legal_en_passant_def
        mirror_position_board_lookup mirror_position_board_none
        mirror_position_board_color has_piece_position_mirror
        has_piece_position_mirror_opponent
        ep_captured_square_mirror position_en_passant_mirror
        pawn_attack_geometry_mirror position_turn_mirror
        mirror_piece_def opponent_involutive opponent_eq_iff EnPassant
        mirror_square_eq_iff split: option.splits)
next
  case WhiteKingCastle
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
next
  case WhiteQueenCastle
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
next
  case BlackKingCastle
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
next
  case BlackQueenCastle
  then show ?thesis by (simp add: pseudo_legal_en_passant_def)
qed

lemma normal_piece_geometry_mirror_record:
  "normal_piece_geometry (mirror_position p) (opponent c)
      \<lparr>piece_color = opponent (piece_color q),
         piece_kind = piece_kind q\<rparr>
      (mirror_square s) (mirror_square t) \<longleftrightarrow>
     normal_piece_geometry p c q s t"
  using normal_piece_geometry_mirror[of p c q s t]
  by (simp add: mirror_piece_def)

lemma normal_pseudo_legal_mirror:
  "normal_pseudo_legal (mirror_position p)
      (mirror_square s) (mirror_square t) \<longleftrightarrow>
     normal_pseudo_legal p s t"
  by (cases "position_board p s"; cases "position_board p t";
      simp add: normal_pseudo_legal_def normal_piece_geometry_mirror
        normal_piece_geometry_mirror_record
        destination_friendly_mirror mirror_position_board_lookup
        mirror_position_board_none mirror_position_board_color
        position_turn_mirror promotion_rank_mirror snd_mirror_square
        mirror_piece_def opponent_involutive opponent_eq_iff
        mirror_rank_eq_iff split: option.splits)

lemma pseudo_legal_mirror:
  "pseudo_legal (mirror_position p) (mirror_move m) \<longleftrightarrow>
     pseudo_legal p m"
proof (cases m)
  case (Normal s t)
  then show ?thesis
    by (simp add: pseudo_legal_def normal_pseudo_legal_mirror Normal)
next
  case (Promotion s t k)
  have h:
      "pseudo_legal_promotion (mirror_position p)
          (mirror_move (Promotion s t k)) \<longleftrightarrow>
       pseudo_legal_promotion p (Promotion s t k)"
    by (rule pseudo_legal_promotion_mirror)
  then show ?thesis
    using Promotion by (simp add: pseudo_legal_def h)
next
  case (EnPassant s t)
  have h:
      "pseudo_legal_en_passant (mirror_position p)
          (mirror_move (EnPassant s t)) \<longleftrightarrow>
       pseudo_legal_en_passant p (EnPassant s t)"
    by (rule pseudo_legal_en_passant_mirror)
  then show ?thesis
    using EnPassant by (simp add: pseudo_legal_def h)
next
  case WhiteKingCastle
  have h:
      "pseudo_legal_castle (mirror_position p)
          (mirror_move WhiteKingCastle) \<longleftrightarrow>
       pseudo_legal_castle p WhiteKingCastle"
    by (rule pseudo_legal_castle_mirror)
  then show ?thesis
    using WhiteKingCastle by (simp add: pseudo_legal_def h)
next
  case WhiteQueenCastle
  have h:
      "pseudo_legal_castle (mirror_position p)
          (mirror_move WhiteQueenCastle) \<longleftrightarrow>
       pseudo_legal_castle p WhiteQueenCastle"
    by (rule pseudo_legal_castle_mirror)
  then show ?thesis
    using WhiteQueenCastle by (simp add: pseudo_legal_def h)
next
  case BlackKingCastle
  have h:
      "pseudo_legal_castle (mirror_position p)
          (mirror_move BlackKingCastle) \<longleftrightarrow>
       pseudo_legal_castle p BlackKingCastle"
    by (rule pseudo_legal_castle_mirror)
  then show ?thesis
    using BlackKingCastle by (simp add: pseudo_legal_def h)
next
  case BlackQueenCastle
  have h:
      "pseudo_legal_castle (mirror_position p)
          (mirror_move BlackQueenCastle) \<longleftrightarrow>
       pseudo_legal_castle p BlackQueenCastle"
    by (rule pseudo_legal_castle_mirror)
  then show ?thesis
    using BlackQueenCastle by (simp add: pseudo_legal_def h)
qed

lemma mirror_square_eq_other:
  "mirror_square u = s \<longleftrightarrow> u = mirror_square s"
  by (metis mirror_square_involutive)

lemma mirror_board_update_eq:
  "mirror_board (board_update b s x) =
     board_update (mirror_board b) (mirror_square s)
       (map_option mirror_piece x)"
proof (rule ext)
  fix u
  show "mirror_board (board_update b s x) u =
      board_update (mirror_board b) (mirror_square s)
        (map_option mirror_piece x) u"
    by (cases "u = mirror_square s";
        simp add: mirror_board_def board_update_def mirror_square_involutive
          mirror_square_eq_other
          mirror_piece_involutive split: option.splits)
qed

lemma mirror_board_move_eq:
  "mirror_board (board_move b s t) =
     board_move (mirror_board b) (mirror_square s) (mirror_square t)"
proof (rule ext)
  fix u
  show "mirror_board (board_move b s t) u =
      board_move (mirror_board b) (mirror_square s) (mirror_square t) u"
    by (cases "u = mirror_square s"; cases "u = mirror_square t";
        simp add: board_move_def mirror_board_def board_update_def
          mirror_square_involutive mirror_square_eq_iff mirror_square_eq_other
          mirror_board_lookup split: option.splits)
qed

lemma moving_piece_mirror:
  "moving_piece (mirror_position p) (mirror_move m) =
     map_option mirror_piece (moving_piece p m)"
  by (simp add: moving_piece_def move_source_mirror
      mirror_position_board_lookup)

lemma moving_color_mirror:
  "moving_color (mirror_position p) (mirror_move m) =
     opponent (moving_color p m)"
  by (cases "moving_piece p m";
      simp add: moving_color_def moving_piece_mirror mirror_piece_def
        position_turn_mirror opponent_involutive)

lemma moving_color_promotion_mirror:
  "moving_color (mirror_position p)
      (Promotion (mirror_square s) (mirror_square t) k) =
     opponent (moving_color p (Promotion s t k))"
  using moving_color_mirror[of p "Promotion s t k"] by simp

lemma move_capture_square_mirror:
  "move_capture_square (mirror_position p) (mirror_move m) =
     map_option mirror_square (move_capture_square p m)"
  by (cases m; simp add: move_capture_square_def
      mirror_position_board_none ep_captured_square_mirror
      position_turn_mirror split: option.splits)

lemma move_is_capture_mirror:
  "move_is_capture (mirror_position p) (mirror_move m) =
     move_is_capture p m"
  by (cases "move_capture_square p m";
      simp add: move_is_capture_def move_capture_square_mirror
        mirror_position_board_none split: option.splits)

lemma move_is_pawn_mirror:
  "move_is_pawn (mirror_position p) (mirror_move m) =
     move_is_pawn p m"
proof (cases m)
  case (Normal s t)
  have h:
      "moving_piece (mirror_position p) (mirror_move (Normal s t)) =
        map_option mirror_piece (moving_piece p (Normal s t))"
    by (rule moving_piece_mirror)
  then show ?thesis using Normal
    by (cases "moving_piece p (Normal s t)";
        simp add: move_is_pawn_def h mirror_piece_def)
next
  case (Promotion s t k)
  then show ?thesis by (simp add: move_is_pawn_def Promotion)
next
  case (EnPassant s t)
  then show ?thesis by (simp add: move_is_pawn_def EnPassant)
next
  case WhiteKingCastle
  have h:
      "moving_piece (mirror_position p) (mirror_move WhiteKingCastle) =
        map_option mirror_piece (moving_piece p WhiteKingCastle)"
    by (rule moving_piece_mirror)
  then show ?thesis using WhiteKingCastle
    by (cases "moving_piece p WhiteKingCastle";
        simp add: move_is_pawn_def h mirror_piece_def)
next
  case WhiteQueenCastle
  have h:
      "moving_piece (mirror_position p) (mirror_move WhiteQueenCastle) =
        map_option mirror_piece (moving_piece p WhiteQueenCastle)"
    by (rule moving_piece_mirror)
  then show ?thesis using WhiteQueenCastle
    by (cases "moving_piece p WhiteQueenCastle";
        simp add: move_is_pawn_def h mirror_piece_def)
next
  case BlackKingCastle
  have h:
      "moving_piece (mirror_position p) (mirror_move BlackKingCastle) =
        map_option mirror_piece (moving_piece p BlackKingCastle)"
    by (rule moving_piece_mirror)
  then show ?thesis using BlackKingCastle
    by (cases "moving_piece p BlackKingCastle";
        simp add: move_is_pawn_def h mirror_piece_def)
next
  case BlackQueenCastle
  have h:
      "moving_piece (mirror_position p) (mirror_move BlackQueenCastle) =
        map_option mirror_piece (moving_piece p BlackQueenCastle)"
    by (rule moving_piece_mirror)
  then show ?thesis using BlackQueenCastle
    by (cases "moving_piece p BlackQueenCastle";
        simp add: move_is_pawn_def h mirror_piece_def)
qed

lemma rights_removed_for_square_mirror:
  "rights_removed_for_square (mirror_square s) =
     mirror_rights (rights_removed_for_square s)"
proof -
  obtain f r where hs: "s = (f,r)" by (cases s) simp
  show ?thesis using hs
    by (cases f; cases r;
        simp add: rights_removed_for_square_def mirror_square_def
          mirror_rights_def)
qed

lemma mirror_rights_diff:
  fixes A B :: castling_rights
  shows "mirror_rights (A - B) = mirror_rights A - mirror_rights B"
proof (rule set_eqI)
  fix r
  show "r \<in> mirror_rights (A - B) \<longleftrightarrow>
      r \<in> mirror_rights A - mirror_rights B"
  proof
    assume h: "r \<in> mirror_rights (A - B)"
    obtain q where hq: "q \<in> A - B" and hqr: "mirror_right q = r"
      using h by (auto simp add: mirror_rights_def)
    have hqa: "r \<in> mirror_rights A"
      using mirror_right_member[of q A] hq hqr by blast
    have hqb: "r \<notin> mirror_rights B"
    proof
      assume hrb: "r \<in> mirror_rights B"
      have hqB: "q \<in> B"
        using mirror_right_member[of q B] hqr hrb by blast
      show False using hq hqB by blast
    qed
    show "r \<in> mirror_rights A - mirror_rights B"
      using hqa hqb by blast
  next
    assume h: "r \<in> mirror_rights A - mirror_rights B"
    have hra: "r \<in> mirror_rights A" using h by simp
    have hrb: "r \<notin> mirror_rights B" using h by simp
    obtain q where hqA: "q \<in> A" and hqr: "mirror_right q = r"
      using hra by (auto simp add: mirror_rights_def)
    have hqB: "q \<notin> B"
    proof
      assume hq: "q \<in> B"
      have "r \<in> mirror_rights B"
        using mirror_right_member[of q B] hq hqr by blast
      then show False using hrb by blast
    qed
    have hq: "q \<in> A - B" using hqA hqB by blast
    show "r \<in> mirror_rights (A - B)"
      using mirror_right_member[of q "A - B"] hq hqr by blast
  qed
qed

lemma mirror_rights_union:
  fixes A B :: castling_rights
  shows "mirror_rights (A \<union> B) = mirror_rights A \<union> mirror_rights B"
  by (simp add: mirror_rights_def image_Un)

lemma mirror_rights_empty:
  "mirror_rights {} = ({} :: castling_rights)"
  by (simp add: mirror_rights_def)

lemma pawn_double_target_mirror:
  "pawn_double_target (opponent c) (mirror_square s) (mirror_square t) =
     map_option mirror_square (pawn_double_target c s t)"
proof -
  obtain sf sr where hs: "s = (sf,sr)" by (cases s) simp
  obtain tf tr where ht: "t = (tf,tr)" by (cases t) simp
  show ?thesis
    using hs ht
    by (cases c; cases sr; cases tr;
        simp add: pawn_double_target_def pawn_double_geometry_def
          mirror_square_def)
qed

lemma pawn_double_target_mirror_white:
  "pawn_double_target Black (mirror_square s) (mirror_square t) =
     map_option mirror_square (pawn_double_target White s t)"
  using pawn_double_target_mirror[of White s t] by simp

lemma pawn_double_target_mirror_black:
  "pawn_double_target White (mirror_square s) (mirror_square t) =
     map_option mirror_square (pawn_double_target Black s t)"
  using pawn_double_target_mirror[of Black s t] by simp

lemma new_en_passant_mirror:
  "new_en_passant (mirror_position p) (mirror_move m) =
     map_option mirror_square (new_en_passant p m)"
proof (cases m)
  case (Normal s t)
  show ?thesis
  proof (cases "position_board p s")
    case None
    then show ?thesis
      by (simp add: new_en_passant_def mirror_position_board_lookup
          mirror_move.simps Normal)
  next
    case (Some q)
    obtain c' k' where hq: "q = \<lparr>piece_color = c', piece_kind = k'\<rparr>"
      by (cases q; simp)
    then show ?thesis
      using Some
      by (cases c'; cases k';
          simp add: new_en_passant_def mirror_position_board_lookup
            pawn_double_target_mirror mirror_piece_def
            pawn_double_target_mirror_white pawn_double_target_mirror_black
            mirror_move.simps Normal)
  qed
next
  case Promotion
  then show ?thesis by (simp add: new_en_passant_def)
next
  case EnPassant
  then show ?thesis by (simp add: new_en_passant_def)
next
  case WhiteKingCastle
  then show ?thesis by (simp add: new_en_passant_def)
next
  case WhiteQueenCastle
  then show ?thesis by (simp add: new_en_passant_def)
next
  case BlackKingCastle
  then show ?thesis by (simp add: new_en_passant_def)
next
  case BlackQueenCastle
  then show ?thesis by (simp add: new_en_passant_def)
qed

lemma rights_removed_for_move_mirror:
  "rights_removed_for_move (mirror_position p) (mirror_move m) =
     mirror_rights (rights_removed_for_move p m)"
proof (cases m)
  case (Normal s t)
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_mirror mirror_rights_union)
next
  case (Promotion s t k)
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_mirror mirror_rights_union)
next
  case (EnPassant s t)
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_mirror mirror_rights_union
        mirror_rights_empty ep_captured_square_mirror position_turn_mirror
        split: option.splits)
next
  case WhiteKingCastle
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_def mirror_rights_def mirror_move.simps)
next
  case WhiteQueenCastle
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_def mirror_rights_def mirror_move.simps)
next
  case BlackKingCastle
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_def mirror_rights_def mirror_move.simps)
next
  case BlackQueenCastle
  then show ?thesis
    by (simp add: rights_removed_for_move_def
        rights_removed_for_square_def mirror_rights_def mirror_move.simps)
qed

lemma rights_after_move_mirror:
  "rights_after_move (mirror_position p) (mirror_move m) =
     mirror_rights (rights_after_move p m)"
  by (simp add: rights_after_move_def position_castling_mirror
      rights_removed_for_move_mirror mirror_rights_diff)

lemma mirror_board_rank1_lookup:
  "mirror_board b (f,R8) = map_option mirror_piece (b (f,R1))"
  using mirror_board_lookup[of b "(f,R1)"]
  by (simp add: mirror_square_def)

lemma mirror_board_rank8_lookup:
  "mirror_board b (f,R1) = map_option mirror_piece (b (f,R8))"
  using mirror_board_lookup[of b "(f,R8)"]
  by (simp add: mirror_square_def)

lemma mirror_position_board_eq:
  "position_board (mirror_position p) =
     mirror_board (position_board p)"
  by (simp add: mirror_position_def)

lemma castle_board_mirror:
  "castle_board (mirror_position p) (mirror_move m) =
     mirror_board (castle_board p m)"
  by (cases m;
      simp add: castle_board_def mirror_position_def
        mirror_board_move_eq mirror_board_update_eq
        castle_rook_source_mirror castle_rook_destination_mirror
        mirror_square_def mirror_board_lookup
        mirror_board_rank1_lookup mirror_board_rank8_lookup
        split: option.splits)

lemma castle_board_white_king_mirror:
  "castle_board (mirror_position p) BlackKingCastle =
     mirror_board (castle_board p WhiteKingCastle)"
  using castle_board_mirror[of p WhiteKingCastle] by simp

lemma castle_board_white_queen_mirror:
  "castle_board (mirror_position p) BlackQueenCastle =
     mirror_board (castle_board p WhiteQueenCastle)"
  using castle_board_mirror[of p WhiteQueenCastle] by simp

lemma castle_board_black_king_mirror:
  "castle_board (mirror_position p) WhiteKingCastle =
     mirror_board (castle_board p BlackKingCastle)"
  using castle_board_mirror[of p BlackKingCastle] by simp

lemma castle_board_black_queen_mirror:
  "castle_board (mirror_position p) WhiteQueenCastle =
     mirror_board (castle_board p BlackQueenCastle)"
  using castle_board_mirror[of p BlackQueenCastle] by simp

lemma apply_board_mirror:
  "apply_board (mirror_position p) (mirror_move m) =
     mirror_board (apply_board p m)"
  by (cases m;
      simp add: apply_board_def mirror_move.simps
        mirror_board_move_eq mirror_board_update_eq castle_board_mirror
        castle_board_white_king_mirror castle_board_white_queen_mirror
        castle_board_black_king_mirror castle_board_black_queen_mirror
        mirror_position_board_eq
        mirror_position_board_lookup mirror_position_board_none
        ep_captured_square_mirror position_turn_mirror
        moving_color_mirror moving_color_promotion_mirror mirror_piece_def
        split: option.splits)

lemma exactly_one_king_exists:
  assumes hk: "exactly_one_king b c"
  shows "\<exists>s \<in> set all_squares. has_piece b s c King"
proof -
  have hc: "card (king_squares b c) = 1"
    using exactly_one_king_card[of b c] hk by simp
  obtain s where hs: "king_squares b c = {s}"
    using hc by (auto simp add: card_1_singleton_iff)
  have hsp: "has_piece b s c King"
    using hs by (simp add: king_squares_def has_piece_iff_squares_of)
  obtain f r where hs': "s = (f,r)" by (cases s) simp
  have hset: "(f,r) \<in> set all_squares"
    by (simp add: all_squares_set)
  show ?thesis
    using hsp hs' hset by blast
qed

lemma exactly_one_king_unique:
  assumes hk: "exactly_one_king b c"
  shows "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
    has_piece b s c King \<longrightarrow>
    has_piece b t c King \<longrightarrow> s = t"
proof -
  have hc: "card (king_squares b c) = 1"
    using exactly_one_king_card[of b c] hk by simp
  obtain u where hu: "king_squares b c = {u}"
    using hc by (auto simp add: card_1_singleton_iff)
  have huniq:
      "\<And>s t. has_piece b s c King \<Longrightarrow>
        has_piece b t c King \<Longrightarrow> s = t"
  proof -
    fix s t
    assume hsp: "has_piece b s c King"
    assume htp: "has_piece b t c King"
    have hsset: "s \<in> king_squares b c"
      using hsp by (simp add: king_squares_def has_piece_iff_squares_of)
    have htset: "t \<in> king_squares b c"
      using htp by (simp add: king_squares_def has_piece_iff_squares_of)
    show "s = t" using hsset htset hu by simp
  qed
  show ?thesis
    using huniq by blast
qed

lemma slider_attack_board_cong:
  assumes hb: "position_board p = position_board q"
  shows "slider_attack p s t \<longleftrightarrow> slider_attack q s t"
  using hb by (simp add: slider_attack_def)

lemma piece_attacks_board_cong:
  assumes hb: "position_board p = position_board q"
  shows "piece_attacks p c s t \<longleftrightarrow> piece_attacks q c s t"
proof (cases "position_board q s")
  case None
  have hpnone: "position_board p s = None"
    using hb None by simp
  then show ?thesis
    using None by (simp add: piece_attacks_def)
next
  case (Some q0)
  obtain c0 k0 where hq0:
      "q0 = \<lparr>piece_color = c0, piece_kind = k0\<rparr>"
    by (cases q0; simp)
  have hp: "position_board p s = Some q0"
    using hb Some by simp
  then show ?thesis
    using Some hq0
    by (cases k0;
        simp add: piece_attacks_def
          slider_attack_board_cong[OF hb])
qed

lemma is_attacked_board_cong:
  assumes hb: "position_board p = position_board q"
  shows "is_attacked p c s \<longleftrightarrow> is_attacked q c s"
proof (rule iffI)
  assume h: "is_attacked p c s"
  have hiff: "is_attacked p c s \<longleftrightarrow>
      (\<exists>u. piece_attacks p c u s)"
    by (rule is_attacked_iff)
  obtain u where hu: "piece_attacks p c u s"
    using h hiff by blast
  show "is_attacked q c s"
  proof (rule iffD2[OF is_attacked_iff])
    show "\<exists>v. piece_attacks q c v s"
      using piece_attacks_board_cong[OF hb, of c u s] hu by blast
  qed
next
  assume h: "is_attacked q c s"
  have hiff: "is_attacked q c s \<longleftrightarrow>
      (\<exists>u. piece_attacks q c u s)"
    by (rule is_attacked_iff)
  obtain u where hu: "piece_attacks q c u s"
    using h hiff by blast
  show "is_attacked p c s"
  proof (rule iffD2[OF is_attacked_iff])
    show "\<exists>v. piece_attacks p c v s"
      using piece_attacks_board_cong[OF hb, of c u s] hu by blast
  qed
qed

lemma in_check_board_cong:
  assumes hb: "position_board p = position_board q"
  shows "in_check p c \<longleftrightarrow> in_check q c"
proof -
  have hk:
      "king_square (position_board p) c =
        king_square (position_board q) c"
    using hb by simp
  show ?thesis
    unfolding in_check_def
    using hk
    by (cases "king_square (position_board q) c";
        simp add: is_attacked_board_cong[OF hb])
qed

lemma in_check_after_move_mirror:
  assumes hp: "position_invariant p"
    and hm: "pseudo_legal p m"
  shows "in_check (apply_move (mirror_position p) (mirror_move m))
      (opponent (position_turn p)) \<longleftrightarrow>
    in_check (apply_move p m) (position_turn p)"
proof -
  have hkW: "exactly_one_king (position_board p) White"
    using hp by (simp add: position_invariant_def)
  have hkB: "exactly_one_king (position_board p) Black"
    using hp by (simp add: position_invariant_def)
  have hpost:
      "exactly_one_king (position_board (apply_move p m))
        (position_turn p)"
  proof (cases "position_turn p")
    case White
    have hpres:
        "exactly_one_king (apply_board p m) White"
      by (rule pseudo_legal_preserves_king_count[OF hm hkW])
    show ?thesis
      using hpres by (simp add: apply_move_board White)
  next
    case Black
    have hpres:
        "exactly_one_king (apply_board p m) Black"
      by (rule pseudo_legal_preserves_king_count[OF hm hkB])
    show ?thesis
      using hpres by (simp add: apply_move_board Black)
  qed
  have hex:
      "\<exists>s \<in> set all_squares.
        has_piece (position_board (apply_move p m)) s
          (position_turn p) King"
    by (rule exactly_one_king_exists[OF hpost])
  have hunique:
      "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
        has_piece (position_board (apply_move p m)) s
          (position_turn p) King \<longrightarrow>
        has_piece (position_board (apply_move p m)) t
          (position_turn p) King \<longrightarrow> s = t"
    by (rule exactly_one_king_unique[OF hpost])
  have hmir:
      "in_check (mirror_position (apply_move p m))
          (opponent (position_turn p)) \<longleftrightarrow>
        in_check (apply_move p m) (position_turn p)"
    by (rule in_check_mirror_unique[OF hex hunique])
  have hboard:
      "position_board (apply_move (mirror_position p) (mirror_move m)) =
        position_board (mirror_position (apply_move p m))"
    by (simp add: apply_move_board apply_board_mirror
        mirror_position_board_eq)
  have hcong:
      "in_check (apply_move (mirror_position p) (mirror_move m))
          (opponent (position_turn p)) \<longleftrightarrow>
        in_check (mirror_position (apply_move p m))
          (opponent (position_turn p))"
    by (rule in_check_board_cong[OF hboard])
  show ?thesis
    using hcong hmir by blast
qed

lemma is_castle_mirror:
  "is_castle (mirror_move m) = is_castle m"
  by (cases m; simp)

lemma legal_move_mirror:
  assumes hp: "position_invariant p"
  shows "legal_move (mirror_position p) (mirror_move m) \<longleftrightarrow>
    legal_move p m"
proof (rule iffI)
  assume hm: "legal_move (mirror_position p) (mirror_move m)"
  have hm_def:
      "pseudo_legal (mirror_position p) (mirror_move m) \<and>
       \<not> in_check (apply_move (mirror_position p) (mirror_move m))
         (position_turn (mirror_position p)) \<and>
       (\<not> is_castle (mirror_move m) \<or>
        castle_safe_squares (mirror_position p) (mirror_move m))"
    using hm by (simp add: legal_move_def)
  have hmp:
      "pseudo_legal (mirror_position p) (mirror_move m)"
    using hm by (simp add: legal_move_def)
  have hpseudo: "pseudo_legal p m"
    using hmp by (simp add: pseudo_legal_mirror)
  have hcheck:
      "in_check (apply_move (mirror_position p) (mirror_move m))
          (opponent (position_turn p)) \<longleftrightarrow>
        in_check (apply_move p m) (position_turn p)"
    by (rule in_check_after_move_mirror[OF hp hpseudo])
  have hsafe:
      "castle_safe_squares (mirror_position p) (mirror_move m) \<longleftrightarrow>
        castle_safe_squares p m"
    by (rule castle_safe_squares_mirror)
  show "legal_move p m"
    unfolding legal_move_def
    using hm_def hpseudo hcheck hsafe
    by (simp add: position_turn_mirror is_castle_mirror; blast)
next
  assume hm: "legal_move p m"
  have hm_def:
      "pseudo_legal p m \<and>
       \<not> in_check (apply_move p m) (position_turn p) \<and>
       (\<not> is_castle m \<or> castle_safe_squares p m)"
    using hm by (simp add: legal_move_def)
  have hpseudo: "pseudo_legal p m"
    using hm by (simp add: legal_move_def)
  have hmp:
      "pseudo_legal (mirror_position p) (mirror_move m)"
    using hpseudo by (simp add: pseudo_legal_mirror)
  have hcheck:
      "in_check (apply_move (mirror_position p) (mirror_move m))
          (opponent (position_turn p)) \<longleftrightarrow>
        in_check (apply_move p m) (position_turn p)"
    by (rule in_check_after_move_mirror[OF hp hpseudo])
  have hsafe:
      "castle_safe_squares (mirror_position p) (mirror_move m) \<longleftrightarrow>
        castle_safe_squares p m"
    by (rule castle_safe_squares_mirror)
  show "legal_move (mirror_position p) (mirror_move m)"
    unfolding legal_move_def
    using hm_def hmp hcheck hsafe
    by (simp add: position_turn_mirror is_castle_mirror; blast)
qed

lemma legal_moves_empty_mirror:
  assumes hp: "position_invariant p"
  shows "legal_moves (mirror_position p) = [] \<longleftrightarrow>
    legal_moves p = []"
proof (rule iffI)
  assume hmir: "legal_moves (mirror_position p) = []"
  show "legal_moves p = []"
  proof (rule ccontr)
    assume hne: "legal_moves p \<noteq> []"
    obtain m l where hlist: "legal_moves p = m # l"
      using hne by (cases "legal_moves p"; simp_all)
    have hm: "m \<in> set (legal_moves p)"
      using hlist by simp
    have hlegal: "legal_move p m"
      using legal_moves_sound hm .
    have hmirror:
        "legal_move (mirror_position p) (mirror_move m)"
      using legal_move_mirror[OF hp, of m] hlegal by blast
    have hmem:
        "mirror_move m \<in> set (legal_moves (mirror_position p))"
      using legal_moves_complete hmirror .
    show False using hmem hmir by simp
  qed
next
  assume hpempty: "legal_moves p = []"
  show "legal_moves (mirror_position p) = []"
  proof (rule ccontr)
    assume hne: "legal_moves (mirror_position p) \<noteq> []"
    obtain m l where hlist:
        "legal_moves (mirror_position p) = m # l"
      using hne by (cases "legal_moves (mirror_position p)"; simp_all)
    have hm:
        "m \<in> set (legal_moves (mirror_position p))"
      using hlist by simp
    have hlegal:
        "legal_move (mirror_position p) m"
      using legal_moves_sound hm .
    have hlegal':
        "legal_move p (mirror_move m)"
      using legal_move_mirror[OF hp, of "mirror_move m"] hlegal
      by (simp add: mirror_move_involutive)
    have hmem:
        "mirror_move m \<in> set (legal_moves p)"
      using legal_moves_complete hlegal' .
    show False using hmem hpempty by simp
  qed
qed

lemma in_check_turn_mirror:
  assumes hp: "position_invariant p"
  shows "in_check (mirror_position p)
      (position_turn (mirror_position p)) \<longleftrightarrow>
    in_check p (position_turn p)"
proof (cases "position_turn p")
  case White
  have hk: "exactly_one_king (position_board p) White"
    using hp by (simp add: position_invariant_def)
  have hex:
      "\<exists>s \<in> set all_squares. has_piece (position_board p) s White King"
    by (rule exactly_one_king_exists[OF hk])
  have hu:
      "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
        has_piece (position_board p) s White King \<longrightarrow>
        has_piece (position_board p) t White King \<longrightarrow> s = t"
    by (rule exactly_one_king_unique[OF hk])
  have h:
      "in_check (mirror_position p) (opponent White) \<longleftrightarrow>
        in_check p White"
    by (rule in_check_mirror_unique[OF hex hu])
  then show ?thesis by (simp add: position_turn_mirror White)
next
  case Black
  have hk: "exactly_one_king (position_board p) Black"
    using hp by (simp add: position_invariant_def)
  have hex:
      "\<exists>s \<in> set all_squares. has_piece (position_board p) s Black King"
    by (rule exactly_one_king_exists[OF hk])
  have hu:
      "\<forall>s \<in> set all_squares. \<forall>t \<in> set all_squares.
        has_piece (position_board p) s Black King \<longrightarrow>
        has_piece (position_board p) t Black King \<longrightarrow> s = t"
    by (rule exactly_one_king_unique[OF hk])
  have h:
      "in_check (mirror_position p) (opponent Black) \<longleftrightarrow>
        in_check p Black"
    by (rule in_check_mirror_unique[OF hex hu])
  then show ?thesis by (simp add: position_turn_mirror Black)
qed

lemma checkmate_mirror:
  assumes hp: "position_invariant p"
  shows "checkmate (mirror_position p) \<longleftrightarrow> checkmate p"
  using in_check_turn_mirror[OF hp] legal_moves_empty_mirror[OF hp]
  by (simp add: checkmate_def)

lemma stalemate_mirror:
  assumes hp: "position_invariant p"
  shows "stalemate (mirror_position p) \<longleftrightarrow> stalemate p"
  using in_check_turn_mirror[OF hp] legal_moves_empty_mirror[OF hp]
  by (simp add: stalemate_def)

end
