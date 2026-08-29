section \<open>Legal chess moves\<close>

theory Chess_Legal
  imports Chess_Pseudo_Legal Chess_Check Chess_Transition
begin

definition legal_move :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "legal_move p m \<longleftrightarrow>
    pseudo_legal p m \<and>
    \<not> in_check (apply_move p m) (position_turn p) \<and>
    (\<not> is_castle m \<or> castle_safe_squares p m)"

lemma has_piece_board_update_other:
  "u \<noteq> s \<Longrightarrow>
   has_piece (board_update b s x) u c k = has_piece b u c k"
  by (simp add: has_piece_def board_update_other)

lemma has_piece_board_move_other:
  "u \<noteq> s \<Longrightarrow> u \<noteq> t \<Longrightarrow>
   has_piece (board_move b s t) u c k = has_piece b u c k"
  by (simp add: board_move_def has_piece_def board_update_def)

lemma legal_move_king_safe:
  "legal_move p m \<Longrightarrow>
     \<not> in_check (apply_move p m) (position_turn p)"
  by (simp add: legal_move_def)

lemma legal_move_pseudo:
  "legal_move p m \<Longrightarrow> pseudo_legal p m"
  by (simp add: legal_move_def)

lemma rights_after_move_not_touched:
  "r \<in> rights_after_move p m \<Longrightarrow>
   r \<notin> rights_removed_for_move p m"
  by (simp add: rights_after_move_def)

lemma rights_removed_for_move_source:
  "r \<in> rights_removed_for_square (move_source m) \<Longrightarrow>
   r \<in> rights_removed_for_move p m"
  by (cases m; simp add: rights_removed_for_move_def)

lemma rights_removed_for_move_destination:
  "r \<in> rights_removed_for_square (move_destination m) \<Longrightarrow>
   r \<in> rights_removed_for_move p m"
  by (cases m; simp add: rights_removed_for_move_def)

lemma rights_removed_for_move_castle_rook_source:
  assumes hs: "castle_rook_source m = Some rs"
    and hr: "r \<in> rights_removed_for_square rs"
  shows "r \<in> rights_removed_for_move p m"
  using hs hr
  by (cases m; simp add: rights_removed_for_move_def)

lemma rights_removed_for_move_castle_rook_destination:
  assumes hs: "castle_rook_destination m = Some rs"
    and hr: "r \<in> rights_removed_for_square rs"
  shows "r \<in> rights_removed_for_move p m"
  using hs hr
  by (cases m; simp add: rights_removed_for_move_def)

lemma rights_removed_for_move_ep_capture:
  assumes hs: "ep_captured_square (position_turn p) t = Some cs"
    and hr: "r \<in> rights_removed_for_square cs"
  shows "r \<in> rights_removed_for_move p (EnPassant s t)"
  using hs hr
  by (simp add: rights_removed_for_move_def)

lemma right_king_removed_at_home:
  "r \<in> rights_removed_for_square (right_king_square r)"
  by (cases r; simp add: rights_removed_for_square_def)

lemma right_rook_removed_at_home:
  "r \<in> rights_removed_for_square (right_rook_square r)"
  by (cases r; simp add: rights_removed_for_square_def)

lemma right_king_not_source:
  assumes hr: "r \<in> rights_after_move p m"
  shows "move_source m \<noteq> right_king_square r"
proof
  assume heq: "move_source m = right_king_square r"
  have hsq: "r \<in> rights_removed_for_square (move_source m)"
    using right_king_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_source[OF hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_rook_not_source:
  assumes hr: "r \<in> rights_after_move p m"
  shows "move_source m \<noteq> right_rook_square r"
proof
  assume heq: "move_source m = right_rook_square r"
  have hsq: "r \<in> rights_removed_for_square (move_source m)"
    using right_rook_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_source[OF hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_king_not_destination:
  assumes hr: "r \<in> rights_after_move p m"
  shows "move_destination m \<noteq> right_king_square r"
proof
  assume heq: "move_destination m = right_king_square r"
  have hsq: "r \<in> rights_removed_for_square (move_destination m)"
    using right_king_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_destination[OF hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_rook_not_destination:
  assumes hr: "r \<in> rights_after_move p m"
  shows "move_destination m \<noteq> right_rook_square r"
proof
  assume heq: "move_destination m = right_rook_square r"
  have hsq: "r \<in> rights_removed_for_square (move_destination m)"
    using right_rook_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_destination[OF hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_king_not_castle_rook_source:
  assumes hr: "r \<in> rights_after_move p m"
    and hs: "castle_rook_source m = Some rs"
  shows "rs \<noteq> right_king_square r"
proof
  assume heq: "rs = right_king_square r"
  have hsq: "r \<in> rights_removed_for_square rs"
    using right_king_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_castle_rook_source[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_rook_not_castle_rook_source:
  assumes hr: "r \<in> rights_after_move p m"
    and hs: "castle_rook_source m = Some rs"
  shows "rs \<noteq> right_rook_square r"
proof
  assume heq: "rs = right_rook_square r"
  have hsq: "r \<in> rights_removed_for_square rs"
    using right_rook_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_castle_rook_source[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_king_not_castle_rook_destination:
  assumes hr: "r \<in> rights_after_move p m"
    and hs: "castle_rook_destination m = Some rs"
  shows "rs \<noteq> right_king_square r"
proof
  assume heq: "rs = right_king_square r"
  have hsq: "r \<in> rights_removed_for_square rs"
    using right_king_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_castle_rook_destination[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_rook_not_castle_rook_destination:
  assumes hr: "r \<in> rights_after_move p m"
    and hs: "castle_rook_destination m = Some rs"
  shows "rs \<noteq> right_rook_square r"
proof
  assume heq: "rs = right_rook_square r"
  have hsq: "r \<in> rights_removed_for_square rs"
    using right_rook_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p m"
    by (rule rights_removed_for_move_castle_rook_destination[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_king_not_ep_capture:
  assumes hr: "r \<in> rights_after_move p (EnPassant s t)"
    and hs: "ep_captured_square (position_turn p) t = Some cs"
  shows "cs \<noteq> right_king_square r"
proof
  assume heq: "cs = right_king_square r"
  have hsq: "r \<in> rights_removed_for_square cs"
    using right_king_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p (EnPassant s t)"
    by (rule rights_removed_for_move_ep_capture[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma right_rook_not_ep_capture:
  assumes hr: "r \<in> rights_after_move p (EnPassant s t)"
    and hs: "ep_captured_square (position_turn p) t = Some cs"
  shows "cs \<noteq> right_rook_square r"
proof
  assume heq: "cs = right_rook_square r"
  have hsq: "r \<in> rights_removed_for_square cs"
    using right_rook_removed_at_home[of r] heq by simp
  have hrem: "r \<in> rights_removed_for_move p (EnPassant s t)"
    by (rule rights_removed_for_move_ep_capture[OF hs hsq])
  show False
    using rights_after_move_not_touched[OF hr] hrem by blast
qed

lemma apply_board_normal_other:
  "u \<noteq> s \<Longrightarrow> u \<noteq> t \<Longrightarrow>
   apply_board p (Normal s t) u = position_board p u"
  by (simp add: apply_board_def board_move_def board_update_def)

lemma apply_board_promotion_other:
  "u \<noteq> s \<Longrightarrow> u \<noteq> t \<Longrightarrow>
   apply_board p (Promotion s t k) u = position_board p u"
  by (simp add: apply_board_def board_update_def)

lemma apply_board_en_passant_other:
  assumes hcs: "ep_captured_square (position_turn p) t = Some cs"
    and hus: "u \<noteq> s" and hut: "u \<noteq> t" and hucs: "u \<noteq> cs"
  shows "apply_board p (EnPassant s t) u = position_board p u"
  using hcs hus hut hucs
  by (simp add: apply_board_def board_move_def board_update_def)

lemma apply_board_castle_other:
  assumes hrs: "castle_rook_source m = Some rs"
    and hrd: "castle_rook_destination m = Some rd"
    and hus: "u \<noteq> move_source m" and hut: "u \<noteq> move_destination m"
    and hurs: "u \<noteq> rs" and hurd: "u \<noteq> rd"
  shows "apply_board p m u = position_board p u"
  using hrs hrd hus hut hurs hurd
  by (cases m; simp add: apply_board_def castle_board_def board_move_def
      board_update_def split: option.splits)

lemma right_home_preserved:
  assumes hr: "r \<in> rights_after_move p m"
    and hk: "has_piece (position_board p) (right_king_square r) (right_color r) King"
    and hrk: "has_piece (position_board p) (right_rook_square r) (right_color r) Rook"
  shows "has_piece (apply_board p m) (right_king_square r) (right_color r) King \<and>
    has_piece (apply_board p m) (right_rook_square r) (right_color r) Rook"
proof (cases m)
  case (Normal s t)
  have hks: "right_king_square r \<noteq> s"
    using right_king_not_source[OF hr] Normal by (simp add: eq_commute)
  have hkt: "right_king_square r \<noteq> t"
    using right_king_not_destination[OF hr] Normal by (simp add: eq_commute)
  have hrs: "right_rook_square r \<noteq> s"
    using right_rook_not_source[OF hr] Normal by (simp add: eq_commute)
  have hrt: "right_rook_square r \<noteq> t"
    using right_rook_not_destination[OF hr] Normal by (simp add: eq_commute)
  have hkb:
      "apply_board p (Normal s t) (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_normal_other[OF hks hkt])
  have hrb:
      "apply_board p (Normal s t) (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_normal_other[OF hrs hrt])
  show ?thesis
    using hk hrk hkb hrb Normal by (simp add: has_piece_def)
next
  case (Promotion s t k)
  have hks: "right_king_square r \<noteq> s"
    using right_king_not_source[OF hr] Promotion by (simp add: eq_commute)
  have hkt: "right_king_square r \<noteq> t"
    using right_king_not_destination[OF hr] Promotion by (simp add: eq_commute)
  have hrs: "right_rook_square r \<noteq> s"
    using right_rook_not_source[OF hr] Promotion by (simp add: eq_commute)
  have hrt: "right_rook_square r \<noteq> t"
    using right_rook_not_destination[OF hr] Promotion by (simp add: eq_commute)
  have hkb:
      "apply_board p (Promotion s t k) (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_promotion_other[OF hks hkt])
  have hrb:
      "apply_board p (Promotion s t k) (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_promotion_other[OF hrs hrt])
  show ?thesis
    using hk hrk hkb hrb Promotion by (simp add: has_piece_def)
next
  case (EnPassant s t)
  have hrE: "r \<in> rights_after_move p (EnPassant s t)"
    using hr EnPassant by simp
  have hks: "right_king_square r \<noteq> s"
    using right_king_not_source[OF hrE] by (simp add: eq_commute)
  have hkt: "right_king_square r \<noteq> t"
    using right_king_not_destination[OF hrE] by (simp add: eq_commute)
  have hrs: "right_rook_square r \<noteq> s"
    using right_rook_not_source[OF hrE] by (simp add: eq_commute)
  have hrt: "right_rook_square r \<noteq> t"
    using right_rook_not_destination[OF hrE] by (simp add: eq_commute)
  show ?thesis
  proof (cases "ep_captured_square (position_turn p) t")
    case None
    have hkb:
        "apply_board p (EnPassant s t) (right_king_square r) =
         position_board p (right_king_square r)"
      using None hks hkt
      by (simp add: apply_board_def board_move_def board_update_def)
    have hrb:
        "apply_board p (EnPassant s t) (right_rook_square r) =
         position_board p (right_rook_square r)"
      using None hrs hrt
      by (simp add: apply_board_def board_move_def board_update_def)
    show ?thesis using hk hrk hkb hrb EnPassant by (simp add: has_piece_def)
  next
    case (Some cs)
    have hcs: "ep_captured_square (position_turn p) t = Some cs"
      using Some .
    have hcsK: "cs \<noteq> right_king_square r"
      using right_king_not_ep_capture[OF hrE hcs] .
    have hcsK': "right_king_square r \<noteq> cs"
      using hcsK by (simp add: eq_commute)
    have hcsR: "cs \<noteq> right_rook_square r"
      using right_rook_not_ep_capture[OF hrE hcs] .
    have hcsR': "right_rook_square r \<noteq> cs"
      using hcsR by (simp add: eq_commute)
    have hkb:
        "apply_board p (EnPassant s t) (right_king_square r) =
         position_board p (right_king_square r)"
      by (rule apply_board_en_passant_other[OF hcs hks hkt hcsK'])
    have hrb:
        "apply_board p (EnPassant s t) (right_rook_square r) =
         position_board p (right_rook_square r)"
      by (rule apply_board_en_passant_other[OF hcs hrs hrt hcsR'])
    show ?thesis using hk hrk hkb hrb EnPassant by (simp add: has_piece_def)
  qed
next
  case WhiteKingCastle
  have hrC: "r \<in> rights_after_move p WhiteKingCastle"
    using hr WhiteKingCastle by simp
  have hkS: "right_king_square r \<noteq> (E,R1)"
    using right_king_not_source[OF hrC] by simp
  have hkD: "right_king_square r \<noteq> (G,R1)"
    using right_king_not_destination[OF hrC] by simp
  have hkRS: "right_king_square r \<noteq> (H,R1)"
    using right_king_not_castle_rook_source[OF hrC] by simp
  have hkRD: "right_king_square r \<noteq> (F,R1)"
    using right_king_not_castle_rook_destination[OF hrC] by simp
  have hrS: "right_rook_square r \<noteq> (E,R1)"
    using right_rook_not_source[OF hrC] by simp
  have hrD: "right_rook_square r \<noteq> (G,R1)"
    using right_rook_not_destination[OF hrC] by simp
  have hrRS: "right_rook_square r \<noteq> (H,R1)"
    using right_rook_not_castle_rook_source[OF hrC] by simp
  have hrRD: "right_rook_square r \<noteq> (F,R1)"
    using right_rook_not_castle_rook_destination[OF hrC] by simp
  have hkb:
      "apply_board p WhiteKingCastle (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_castle_other[where p = p and m = WhiteKingCastle
          and u = "right_king_square r" and rs = "(H,R1)" and rd = "(F,R1)"];
        simp add: hkS hkD hkRS hkRD)
  have hrb:
      "apply_board p WhiteKingCastle (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_castle_other[where p = p and m = WhiteKingCastle
          and u = "right_rook_square r" and rs = "(H,R1)" and rd = "(F,R1)"];
        simp add: hrS hrD hrRS hrRD)
  show ?thesis using hk hrk hkb hrb WhiteKingCastle by (simp add: has_piece_def)
next
  case WhiteQueenCastle
  have hrC: "r \<in> rights_after_move p WhiteQueenCastle"
    using hr WhiteQueenCastle by simp
  have hkS: "right_king_square r \<noteq> (E,R1)"
    using right_king_not_source[OF hrC] by simp
  have hkD: "right_king_square r \<noteq> (C,R1)"
    using right_king_not_destination[OF hrC] by simp
  have hkRS: "right_king_square r \<noteq> (A,R1)"
    using right_king_not_castle_rook_source[OF hrC] by simp
  have hkRD: "right_king_square r \<noteq> (D,R1)"
    using right_king_not_castle_rook_destination[OF hrC] by simp
  have hrS: "right_rook_square r \<noteq> (E,R1)"
    using right_rook_not_source[OF hrC] by simp
  have hrD: "right_rook_square r \<noteq> (C,R1)"
    using right_rook_not_destination[OF hrC] by simp
  have hrRS: "right_rook_square r \<noteq> (A,R1)"
    using right_rook_not_castle_rook_source[OF hrC] by simp
  have hrRD: "right_rook_square r \<noteq> (D,R1)"
    using right_rook_not_castle_rook_destination[OF hrC] by simp
  have hkb:
      "apply_board p WhiteQueenCastle (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_castle_other[where p = p and m = WhiteQueenCastle
          and u = "right_king_square r" and rs = "(A,R1)" and rd = "(D,R1)"];
        simp add: hkS hkD hkRS hkRD)
  have hrb:
      "apply_board p WhiteQueenCastle (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_castle_other[where p = p and m = WhiteQueenCastle
          and u = "right_rook_square r" and rs = "(A,R1)" and rd = "(D,R1)"];
        simp add: hrS hrD hrRS hrRD)
  show ?thesis using hk hrk hkb hrb WhiteQueenCastle by (simp add: has_piece_def)
next
  case BlackKingCastle
  have hrC: "r \<in> rights_after_move p BlackKingCastle"
    using hr BlackKingCastle by simp
  have hkS: "right_king_square r \<noteq> (E,R8)"
    using right_king_not_source[OF hrC] by simp
  have hkD: "right_king_square r \<noteq> (G,R8)"
    using right_king_not_destination[OF hrC] by simp
  have hkRS: "right_king_square r \<noteq> (H,R8)"
    using right_king_not_castle_rook_source[OF hrC] by simp
  have hkRD: "right_king_square r \<noteq> (F,R8)"
    using right_king_not_castle_rook_destination[OF hrC] by simp
  have hrS: "right_rook_square r \<noteq> (E,R8)"
    using right_rook_not_source[OF hrC] by simp
  have hrD: "right_rook_square r \<noteq> (G,R8)"
    using right_rook_not_destination[OF hrC] by simp
  have hrRS: "right_rook_square r \<noteq> (H,R8)"
    using right_rook_not_castle_rook_source[OF hrC] by simp
  have hrRD: "right_rook_square r \<noteq> (F,R8)"
    using right_rook_not_castle_rook_destination[OF hrC] by simp
  have hkb:
      "apply_board p BlackKingCastle (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_castle_other[where p = p and m = BlackKingCastle
          and u = "right_king_square r" and rs = "(H,R8)" and rd = "(F,R8)"];
        simp add: hkS hkD hkRS hkRD)
  have hrb:
      "apply_board p BlackKingCastle (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_castle_other[where p = p and m = BlackKingCastle
          and u = "right_rook_square r" and rs = "(H,R8)" and rd = "(F,R8)"];
        simp add: hrS hrD hrRS hrRD)
  show ?thesis using hk hrk hkb hrb BlackKingCastle by (simp add: has_piece_def)
next
  case BlackQueenCastle
  have hrC: "r \<in> rights_after_move p BlackQueenCastle"
    using hr BlackQueenCastle by simp
  have hkS: "right_king_square r \<noteq> (E,R8)"
    using right_king_not_source[OF hrC] by simp
  have hkD: "right_king_square r \<noteq> (C,R8)"
    using right_king_not_destination[OF hrC] by simp
  have hkRS: "right_king_square r \<noteq> (A,R8)"
    using right_king_not_castle_rook_source[OF hrC] by simp
  have hkRD: "right_king_square r \<noteq> (D,R8)"
    using right_king_not_castle_rook_destination[OF hrC] by simp
  have hrS: "right_rook_square r \<noteq> (E,R8)"
    using right_rook_not_source[OF hrC] by simp
  have hrD: "right_rook_square r \<noteq> (C,R8)"
    using right_rook_not_destination[OF hrC] by simp
  have hrRS: "right_rook_square r \<noteq> (A,R8)"
    using right_rook_not_castle_rook_source[OF hrC] by simp
  have hrRD: "right_rook_square r \<noteq> (D,R8)"
    using right_rook_not_castle_rook_destination[OF hrC] by simp
  have hkb:
      "apply_board p BlackQueenCastle (right_king_square r) =
       position_board p (right_king_square r)"
    by (rule apply_board_castle_other[where p = p and m = BlackQueenCastle
          and u = "right_king_square r" and rs = "(A,R8)" and rd = "(D,R8)"];
        simp add: hkS hkD hkRS hkRD)
  have hrb:
      "apply_board p BlackQueenCastle (right_rook_square r) =
       position_board p (right_rook_square r)"
    by (rule apply_board_castle_other[where p = p and m = BlackQueenCastle
          and u = "right_rook_square r" and rs = "(A,R8)" and rd = "(D,R8)"];
        simp add: hrS hrD hrRS hrRD)
  show ?thesis using hk hrk hkb hrb BlackQueenCastle by (simp add: has_piece_def)
qed

lemma legal_castle_safe_squares:
  "legal_move p m \<Longrightarrow> is_castle m \<Longrightarrow>
     castle_safe_squares p m"
  by (simp add: legal_move_def)

lemma legal_move_preserves_rights_consistent:
  assumes hp: "position_invariant p"
    and hm: "legal_move p m"
  shows "rights_consistent (apply_move p m)"
proof -
  have hrc: "rights_consistent p"
    using hp by (simp add: position_invariant_def)
  have hpost:
      "\<forall>r \<in> position_castling (apply_move p m).
        has_piece (position_board (apply_move p m))
          (right_king_square r) (right_color r) King \<and>
        has_piece (position_board (apply_move p m))
          (right_rook_square r) (right_color r) Rook"
  proof
    fix r
    assume hr: "r \<in> position_castling (apply_move p m)"
    have hrm: "r \<in> rights_after_move p m"
      using hr by (simp add: apply_move_def)
    have hold: "r \<in> position_castling p"
      using rights_after_move_member_old[OF hrm] .
    have hh: "has_piece (position_board p) (right_king_square r) (right_color r) King \<and>
        has_piece (position_board p) (right_rook_square r) (right_color r) Rook"
      using hrc hold by (cases r; simp add: rights_consistent_def)
    have hpres:
        "has_piece (apply_board p m) (right_king_square r) (right_color r) King \<and>
         has_piece (apply_board p m) (right_rook_square r) (right_color r) Rook"
      using right_home_preserved[OF hrm] hh by blast
    show "has_piece (position_board (apply_move p m))
          (right_king_square r) (right_color r) King \<and>
        has_piece (position_board (apply_move p m))
          (right_rook_square r) (right_color r) Rook"
      using hpres by (simp add: apply_move_board)
  qed
  show "rights_consistent (apply_move p m)"
    using rights_consistent_iff[of "apply_move p m"] hpost by blast
qed

lemma pawn_move_white_not_R1:
  "pawn_move_geometry White s t \<Longrightarrow> snd t \<noteq> R1"
proof -
  assume h: "pawn_move_geometry White s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R1"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_move_geometry_def rank_index_cases)
qed

lemma pawn_attack_white_not_R1:
  "pawn_attack_geometry White s t \<Longrightarrow> snd t \<noteq> R1"
proof -
  assume h: "pawn_attack_geometry White s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R1"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_attack_geometry_def rank_index_cases)
qed

lemma pawn_double_white_not_R1:
  "pawn_double_geometry White s t \<Longrightarrow> snd t \<noteq> R1"
proof -
  assume h: "pawn_double_geometry White s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R1"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_double_geometry_def rank_index_cases)
qed

lemma pawn_move_black_not_R8:
  "pawn_move_geometry Black s t \<Longrightarrow> snd t \<noteq> R8"
proof -
  assume h: "pawn_move_geometry Black s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R8"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_move_geometry_def rank_index_cases)
qed

lemma pawn_attack_black_not_R8:
  "pawn_attack_geometry Black s t \<Longrightarrow> snd t \<noteq> R8"
proof -
  assume h: "pawn_attack_geometry Black s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R8"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_attack_geometry_def rank_index_cases)
qed

lemma pawn_double_black_not_R8:
  "pawn_double_geometry Black s t \<Longrightarrow> snd t \<noteq> R8"
proof -
  assume h: "pawn_double_geometry Black s t"
  obtain sf sr where hs: "s = (sf, sr)" by (cases s; simp)
  obtain tf tr where ht: "t = (tf, tr)" by (cases t; simp)
  show "snd t \<noteq> R8"
    using h hs ht by (cases sr; cases tr; simp add: hs ht pawn_double_geometry_def rank_index_cases)
qed

lemma normal_move_preserves_pawn_rank:
  assumes hn: "normal_pseudo_legal p s t"
    and hno: "\<not> pawn_on_promotion_rank (position_board p)"
  shows "\<not> pawn_on_promotion_rank (apply_board p (Normal s t))"
proof -
  show "\<not> pawn_on_promotion_rank (apply_board p (Normal s t))"
  proof
  have st: "s \<noteq> t"
    using normal_pseudo_legal_source_destination hn by blast
  have hsrc:
      "\<And>q. position_board p s = Some q \<Longrightarrow>
       piece_kind q = Pawn \<Longrightarrow> snd t \<noteq> promotion_rank (position_turn p)"
    using hn by (auto simp add: normal_pseudo_legal_def split: option.splits)
  have hsrcdir:
      "\<And>q. position_board p s = Some q \<Longrightarrow>
       piece_kind q = Pawn \<Longrightarrow>
       ((position_turn p = White \<longrightarrow> snd t \<noteq> R1) \<and>
        (position_turn p = Black \<longrightarrow> snd t \<noteq> R8))"
  proof -
    fix q
    assume hq: "position_board p s = Some q"
      and hkind: "piece_kind q = Pawn"
    have hgeom:
        "pawn_move_geometry (position_turn p) s t \<or>
         pawn_attack_geometry (position_turn p) s t \<or>
         pawn_double_geometry (position_turn p) s t"
      using hn hq hkind
      by (auto simp add: normal_pseudo_legal_def normal_piece_geometry_def
          split: option.splits)
    show "(position_turn p = White \<longrightarrow> snd t \<noteq> R1) \<and>
          (position_turn p = Black \<longrightarrow> snd t \<noteq> R8)"
    proof (cases "position_turn p")
      case White
      have hgeomW:
          "pawn_move_geometry White s t \<or>
           pawn_attack_geometry White s t \<or>
           pawn_double_geometry White s t"
        using hgeom White by simp
      have hwhite:
          "snd t \<noteq> R1"
        using hgeomW by (auto dest: pawn_move_white_not_R1
          pawn_attack_white_not_R1 pawn_double_white_not_R1)
      show ?thesis using White hwhite by simp
    next
      case Black
      have hgeomB:
          "pawn_move_geometry Black s t \<or>
           pawn_attack_geometry Black s t \<or>
           pawn_double_geometry Black s t"
        using hgeom Black by simp
      have hblack:
          "snd t \<noteq> R8"
        using hgeomB by (auto dest: pawn_move_black_not_R8
          pawn_attack_black_not_R8 pawn_double_black_not_R8)
      show ?thesis using Black hblack by simp
    qed
  qed
  have hno':
      "\<forall>u \<in> set all_squares.
       \<not> (case position_board p u of
          Some q \<Rightarrow> piece_kind q = Pawn \<and>
            (snd u = R1 \<or> snd u = R8)
        | None \<Rightarrow> False)"
    using hno by (simp add: pawn_on_promotion_rank_iff)
  assume hbad: "pawn_on_promotion_rank (apply_board p (Normal s t))"
  obtain u where hu: "u \<in> set all_squares"
    and hpu:
      "(case apply_board p (Normal s t) u of
         Some q \<Rightarrow> piece_kind q = Pawn \<and>
           (snd u = R1 \<or> snd u = R8)
       | None \<Rightarrow> False)"
    using hbad by (simp add: pawn_on_promotion_rank_iff) blast
  have ucases: "u = s \<or> u = t \<or> (u \<noteq> s \<and> u \<noteq> t)"
    by blast
  have hcase_s: "u = s \<Longrightarrow> False"
    using hpu st by (simp add: apply_board_def board_move_def board_update_def)
  have hcase_t: "u = t \<Longrightarrow> False"
  proof -
    assume hut: "u = t"
    have hbt: "apply_board p (Normal s t) u = position_board p s"
      using hut by (simp add: apply_board_def board_move_destination)
    obtain q where hq: "position_board p s = Some q"
      and hqkind: "piece_kind q = Pawn"
      and hfinal: "snd t = R1 \<or> snd t = R8"
      using hpu hbt hut by (auto split: option.splits)
    have hprom: "snd t \<noteq> promotion_rank (position_turn p)"
      using hsrc hq hqkind by blast
    show False
      using hprom hfinal hsrcdir hq hqkind
      by (cases "position_turn p"; simp add: promotion_rank_def)
  qed
  have hcase_other: "u \<noteq> s \<and> u \<noteq> t \<Longrightarrow> False"
  proof -
    assume hother: "u \<noteq> s \<and> u \<noteq> t"
    have hsame: "apply_board p (Normal s t) u = position_board p u"
      using hother by (simp add: apply_board_def board_move_def board_update_def)
    have hpu_old:
        "(case position_board p u of
           Some q \<Rightarrow> piece_kind q = Pawn \<and>
             (snd u = R1 \<or> snd u = R8)
         | None \<Rightarrow> False)"
      using hpu hsame by simp
    show False using hno' hu hpu_old by blast
  qed
  have hfalse: "False"
    using ucases hcase_s hcase_t hcase_other
    by (auto simp add: hcase_s hcase_t hcase_other)
  show False by (rule hfalse)
  qed
qed

lemma legal_move_turn:
  "legal_move p m \<Longrightarrow>
     position_turn (apply_move p m) = opponent (position_turn p)"
  by (simp add: turn_apply_move)

lemma promotion_move_preserves_pawn_rank:
  assumes hp: "pseudo_legal_promotion p (Promotion s t k)"
    and hno: "\<not> pawn_on_promotion_rank (position_board p)"
  shows "\<not> pawn_on_promotion_rank
    (apply_board p (Promotion s t k))"
proof -
  have hpk: "promotion_piece_kind k \<noteq> Pawn"
    by (cases k; simp)
  show ?thesis
    using hp hno
    by (auto simp add: pawn_on_promotion_rank_iff apply_board_def
        board_update_def hpk split: option.splits if_splits)
qed

lemma en_passant_move_preserves_pawn_rank:
  assumes he: "pseudo_legal_en_passant p (EnPassant s t)"
    and hno: "\<not> pawn_on_promotion_rank (position_board p)"
  shows "\<not> pawn_on_promotion_rank
    (apply_board p (EnPassant s t))"
  using he hno
  by (auto simp add: pawn_on_promotion_rank_iff apply_board_def
      board_move_def board_update_def pseudo_legal_en_passant_def
      ep_captured_square_def pawn_attack_geometry_def split: option.splits
      if_splits)

lemma castle_move_preserves_pawn_rank:
  assumes hc: "pseudo_legal_castle p m"
    and hno: "\<not> pawn_on_promotion_rank (position_board p)"
  shows "\<not> pawn_on_promotion_rank (apply_board p m)"
  using hc hno
  by (cases m; auto simp add: pawn_on_promotion_rank_iff apply_board_def
      castle_board_def board_move_def board_update_def
      pseudo_legal_castle_def castle_clear_def castle_empty_squares_def
      has_piece_def split: option.splits if_splits)

lemma pseudo_legal_preserves_pawn_rank:
  assumes hm: "pseudo_legal p m"
    and hno: "\<not> pawn_on_promotion_rank (position_board p)"
  shows "\<not> pawn_on_promotion_rank (apply_board p m)"
proof (cases m)
  case (Normal s t)
  show ?thesis
    using normal_move_preserves_pawn_rank[of p s t, OF _ hno] hm Normal
    by (simp add: pseudo_legal_def)
next
  case (Promotion s t k)
  show ?thesis
    using promotion_move_preserves_pawn_rank[of p s t k, OF _ hno] hm Promotion
    by (simp add: pseudo_legal_def)
next
  case (EnPassant s t)
  show ?thesis
    using en_passant_move_preserves_pawn_rank[of p s t, OF _ hno] hm EnPassant
    by (simp add: pseudo_legal_def)
next
  case WhiteKingCastle
  show ?thesis
    using castle_move_preserves_pawn_rank[of p WhiteKingCastle, OF _ hno]
      hm WhiteKingCastle by (simp add: pseudo_legal_def)
next
  case WhiteQueenCastle
  show ?thesis
    using castle_move_preserves_pawn_rank[of p WhiteQueenCastle, OF _ hno]
      hm WhiteQueenCastle by (simp add: pseudo_legal_def)
next
  case BlackKingCastle
  show ?thesis
    using castle_move_preserves_pawn_rank[of p BlackKingCastle, OF _ hno]
      hm BlackKingCastle by (simp add: pseudo_legal_def)
next
  case BlackQueenCastle
  show ?thesis
    using castle_move_preserves_pawn_rank[of p BlackQueenCastle, OF _ hno]
      hm BlackQueenCastle by (simp add: pseudo_legal_def)
qed

lemma normal_move_preserves_king_count:
  assumes hn: "normal_pseudo_legal p s t"
    and hk: "exactly_one_king (position_board p) c"
  shows "exactly_one_king (apply_board p (Normal s t)) c"
proof -
  have st: "s \<noteq> t"
    using normal_pseudo_legal_source_destination hn by blast
  have ht: "\<not> has_piece (position_board p) t c King"
    using normal_pseudo_legal_destination_no_king hn by blast
  have hboard:
      "apply_board p (Normal s t) = board_move (position_board p) s t"
    by (simp add: apply_board_def)
  show ?thesis
    using hboard exactly_one_king_board_move[OF st hk ht] by simp
qed

lemma promotion_move_preserves_king_count:
  assumes hp: "pseudo_legal_promotion p (Promotion s t k)"
    and hk: "exactly_one_king (position_board p) c"
  shows "exactly_one_king (apply_board p (Promotion s t k)) c"
proof -
  have hs: "\<not> has_piece (position_board p) s c King"
    using hp by (auto simp add: pseudo_legal_promotion_def has_piece_def
      split: option.splits)
  have hs_new:
      "\<not> has_piece (board_update (position_board p) s None) s c King"
    by (simp add: has_piece_def board_update_def)
  have ht: "\<not> has_piece (board_update (position_board p) s None) t c King"
    using hp by (auto simp add: pseudo_legal_promotion_def has_piece_def
      board_update_def split: option.splits)
  have ht_new:
      "\<not> has_piece
        (board_update (board_update (position_board p) s None) t
          (Some \<lparr>piece_color = moving_color p (Promotion s t k),
             piece_kind = promotion_piece_kind k\<rparr>)) t c King"
  proof -
    have pk: "promotion_piece_kind k \<noteq> King"
      by (cases k; simp)
    show ?thesis
      by (simp add: has_piece_def board_update_def pk)
  qed
  have hking:
      "exactly_one_king
        (board_update (board_update (position_board p) s None) t
          (Some \<lparr>piece_color = moving_color p (Promotion s t k),
             piece_kind = promotion_piece_kind k\<rparr>)) c"
    by (rule exactly_one_king_two_updates[OF hk hs hs_new ht ht_new])
  show ?thesis
    using hking by (simp add: apply_board_def)
qed

lemma en_passant_move_preserves_king_count:
  assumes he: "pseudo_legal_en_passant p (EnPassant s t)"
    and hk: "exactly_one_king (position_board p) c"
  shows "exactly_one_king (apply_board p (EnPassant s t)) c"
proof -
  have hcs: "\<exists>cs. ep_captured_square (position_turn p) t = Some cs"
    using he by (auto simp add: pseudo_legal_en_passant_def split: option.splits)
  then obtain cs where hcs: "ep_captured_square (position_turn p) t = Some cs"
    by blast
  have st: "s \<noteq> t"
    using he by (auto simp add: pseudo_legal_en_passant_def
      pawn_attack_geometry_def split: option.splits)
  have ht: "\<not> has_piece (position_board p) t c King"
    using he by (auto simp add: pseudo_legal_en_passant_def has_piece_def
      split: option.splits)
  have hfirst: "exactly_one_king
      (board_move (position_board p) s t) c"
    by (rule exactly_one_king_board_move[OF st hk ht])
  have hcs_old:
      "\<not> has_piece (board_move (position_board p) s t) cs c King"
    using he hcs by (auto simp add: pseudo_legal_en_passant_def
      has_piece_def board_move_def board_update_def ep_captured_square_def
      split: option.splits if_splits)
  have hcs_new:
      "\<not> has_piece (board_update (board_move (position_board p) s t) cs None)
        cs c King"
    by (simp add: has_piece_def board_update_def)
  have hfinal: "exactly_one_king
      (board_update (board_move (position_board p) s t) cs None) c"
    by (rule exactly_one_king_board_update_unchanged[OF hfirst hcs_old hcs_new])
  show ?thesis
    using hfinal hcs by (simp add: apply_board_def)
qed

lemma castle_board_preserves_king_count:
  assumes hk: "exactly_one_king b c"
    and st: "ks \<noteq> kt"
    and ht: "\<not> has_piece b kt c King"
    and rs_ks: "rs \<noteq> ks"
    and rs_kt: "rs \<noteq> kt"
    and rd_ks: "rd \<noteq> ks"
    and rd_kt: "rd \<noteq> kt"
    and rs_rd: "rs \<noteq> rd"
    and hrs: "\<not> has_piece b rs c King"
    and hrd: "\<not> has_piece b rd c King"
  shows "exactly_one_king
      (board_update (board_update (board_move b ks kt) rs None) rd (b rs)) c"
proof -
  have hfirst: "exactly_one_king (board_move b ks kt) c"
    by (rule exactly_one_king_board_move[OF st hk ht])
  have hrs': "\<not> has_piece (board_move b ks kt) rs c King"
    using hrs rs_ks rs_kt by (simp add: has_piece_def board_move_def board_update_def)
  have hrs_new:
      "\<not> has_piece (board_update (board_move b ks kt) rs None) rs c King"
    by (simp add: has_piece_def board_update_def)
  have hmid: "exactly_one_king (board_update (board_move b ks kt) rs None) c"
    by (rule exactly_one_king_board_update_unchanged[OF hfirst hrs' hrs_new])
  have hrd': "\<not> has_piece (board_update (board_move b ks kt) rs None) rd c King"
    using hrd rd_ks rd_kt rs_rd by
      (simp add: has_piece_def board_move_def board_update_def)
  have hrd_new:
      "\<not> has_piece
        (board_update (board_update (board_move b ks kt) rs None) rd (b rs))
        rd c King"
    using hrs by (simp add: has_piece_def board_update_def)
  show ?thesis
    by (rule exactly_one_king_board_update_unchanged[OF hmid hrd' hrd_new])
qed

lemma castle_move_preserves_king_count:
  assumes hc: "pseudo_legal_castle p m"
    and hk: "exactly_one_king (position_board p) c"
  shows "exactly_one_king (apply_board p m) c"
proof (cases m)
  case WhiteKingCastle
  have hG: "position_board p (G, R1) = None"
    using hc WhiteKingCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have hF: "position_board p (F, R1) = None"
    using hc WhiteKingCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have ht: "\<not> has_piece (position_board p) (G, R1) c King"
    using hG by (simp add: has_piece_def)
  have hrs: "\<not> has_piece (position_board p) (H, R1) c King"
    using hc WhiteKingCastle by (auto simp add: pseudo_legal_castle_def has_piece_def split: option.splits)
  have hrd: "\<not> has_piece (position_board p) (F, R1) c King"
    using hF by (simp add: has_piece_def)
  have hcastle:
      "exactly_one_king
        (board_update (board_update
          (board_move (position_board p) (E,R1) (G,R1)) (H,R1) None)
          (F,R1) (position_board p (H,R1))) c"
    by (rule castle_board_preserves_king_count[OF hk]; simp add: hrs hrd ht)
  then show ?thesis using WhiteKingCastle by (simp add: apply_board_def castle_board_def)
next
  case WhiteQueenCastle
  have hC: "position_board p (C, R1) = None"
    using hc WhiteQueenCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have hD: "position_board p (D, R1) = None"
    using hc WhiteQueenCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have ht: "\<not> has_piece (position_board p) (C, R1) c King"
    using hC by (simp add: has_piece_def)
  have hrs: "\<not> has_piece (position_board p) (A, R1) c King"
    using hc WhiteQueenCastle by (auto simp add: pseudo_legal_castle_def has_piece_def split: option.splits)
  have hrd: "\<not> has_piece (position_board p) (D, R1) c King"
    using hD by (simp add: has_piece_def)
  have hcastle:
      "exactly_one_king
        (board_update (board_update
          (board_move (position_board p) (E,R1) (C,R1)) (A,R1) None)
          (D,R1) (position_board p (A,R1))) c"
    by (rule castle_board_preserves_king_count[OF hk]; simp add: hrs hrd ht)
  then show ?thesis using WhiteQueenCastle by (simp add: apply_board_def castle_board_def)
next
  case BlackKingCastle
  have hG: "position_board p (G, R8) = None"
    using hc BlackKingCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have hF: "position_board p (F, R8) = None"
    using hc BlackKingCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have ht: "\<not> has_piece (position_board p) (G, R8) c King"
    using hG by (simp add: has_piece_def)
  have hrs: "\<not> has_piece (position_board p) (H, R8) c King"
    using hc BlackKingCastle by (auto simp add: pseudo_legal_castle_def has_piece_def split: option.splits)
  have hrd: "\<not> has_piece (position_board p) (F, R8) c King"
    using hF by (simp add: has_piece_def)
  have hcastle:
      "exactly_one_king
        (board_update (board_update
          (board_move (position_board p) (E,R8) (G,R8)) (H,R8) None)
          (F,R8) (position_board p (H,R8))) c"
    by (rule castle_board_preserves_king_count[OF hk]; simp add: hrs hrd ht)
  then show ?thesis using BlackKingCastle by (simp add: apply_board_def castle_board_def)
next
  case BlackQueenCastle
  have hC: "position_board p (C, R8) = None"
    using hc BlackQueenCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have hD: "position_board p (D, R8) = None"
    using hc BlackQueenCastle by (auto simp add: pseudo_legal_castle_def
      castle_clear_def castle_empty_squares_def)
  have ht: "\<not> has_piece (position_board p) (C, R8) c King"
    using hC by (simp add: has_piece_def)
  have hrs: "\<not> has_piece (position_board p) (A, R8) c King"
    using hc BlackQueenCastle by (auto simp add: pseudo_legal_castle_def has_piece_def split: option.splits)
  have hrd: "\<not> has_piece (position_board p) (D, R8) c King"
    using hD by (simp add: has_piece_def)
  have hcastle:
      "exactly_one_king
        (board_update (board_update
          (board_move (position_board p) (E,R8) (C,R8)) (A,R8) None)
          (D,R8) (position_board p (A,R8))) c"
    by (rule castle_board_preserves_king_count[OF hk]; simp add: hrs hrd ht)
  then show ?thesis using BlackQueenCastle by (simp add: apply_board_def castle_board_def)
next
  case Normal
  then show ?thesis using hc by (simp add: pseudo_legal_castle_def)
next
  case Promotion
  then show ?thesis using hc by (simp add: pseudo_legal_castle_def)
next
  case EnPassant
  then show ?thesis using hc by (simp add: pseudo_legal_castle_def)
qed

lemma pseudo_legal_preserves_king_count:
  assumes hm: "pseudo_legal p m"
    and hk: "exactly_one_king (position_board p) c"
  shows "exactly_one_king (apply_board p m) c"
proof (cases m)
  case (Normal s t)
  have hn: "normal_pseudo_legal p s t"
    using hm Normal by (simp add: pseudo_legal_def)
  show ?thesis
    using normal_move_preserves_king_count[OF hn hk] Normal
    by simp
next
  case (Promotion s t k)
  have hp: "pseudo_legal_promotion p (Promotion s t k)"
    using hm Promotion by (simp add: pseudo_legal_def)
  show ?thesis
    using promotion_move_preserves_king_count[OF hp hk] Promotion
    by simp
next
  case (EnPassant s t)
  have he: "pseudo_legal_en_passant p (EnPassant s t)"
    using hm EnPassant by (simp add: pseudo_legal_def)
  show ?thesis
    using en_passant_move_preserves_king_count[OF he hk] EnPassant
    by simp
next
  case WhiteKingCastle
  have hc: "pseudo_legal_castle p WhiteKingCastle"
    using hm WhiteKingCastle by (simp add: pseudo_legal_def)
  show ?thesis
    using castle_move_preserves_king_count[OF hc hk] WhiteKingCastle by simp
next
  case WhiteQueenCastle
  have hc: "pseudo_legal_castle p WhiteQueenCastle"
    using hm WhiteQueenCastle by (simp add: pseudo_legal_def)
  show ?thesis
    using castle_move_preserves_king_count[OF hc hk] WhiteQueenCastle by simp
next
  case BlackKingCastle
  have hc: "pseudo_legal_castle p BlackKingCastle"
    using hm BlackKingCastle by (simp add: pseudo_legal_def)
  show ?thesis
    using castle_move_preserves_king_count[OF hc hk] BlackKingCastle by simp
next
  case BlackQueenCastle
  have hc: "pseudo_legal_castle p BlackQueenCastle"
    using hm BlackQueenCastle by (simp add: pseudo_legal_def)
  show ?thesis
    using castle_move_preserves_king_count[OF hc hk] BlackQueenCastle by simp
qed

lemma legal_move_preserves_king_count:
  assumes hp: "position_invariant p"
    and hm: "legal_move p m"
  shows "exactly_one_king (position_board (apply_move p m)) White \<and>
         exactly_one_king (position_board (apply_move p m)) Black"
proof -
  have hkW: "exactly_one_king (position_board p) White"
    using hp by (simp add: position_invariant_def)
  have hkB: "exactly_one_king (position_board p) Black"
    using hp by (simp add: position_invariant_def)
  have hwhite:
      "exactly_one_king (apply_board p m) White"
    by (rule pseudo_legal_preserves_king_count[OF legal_move_pseudo[OF hm] hkW])
  have hblack:
      "exactly_one_king (apply_board p m) Black"
    by (rule pseudo_legal_preserves_king_count[OF legal_move_pseudo[OF hm] hkB])
  show ?thesis
    using hwhite hblack apply_move_board by simp
qed

lemma legal_move_preserves_fullmove_positive:
  assumes hp: "position_invariant p"
    and hm: "legal_move p m"
  shows "position_fullmove (apply_move p m) > 0"
  using hp by (simp add: position_invariant_def fullmove_clock_apply_move)

lemma legal_move_preserves_core_position_invariant:
  assumes hp: "position_invariant p"
    and hm: "legal_move p m"
  shows "exactly_one_king (position_board (apply_move p m)) White \<and>
         exactly_one_king (position_board (apply_move p m)) Black \<and>
         \<not> pawn_on_promotion_rank (position_board (apply_move p m)) \<and>
         position_fullmove (apply_move p m) > 0"
proof -
  have hking:
      "exactly_one_king (position_board (apply_move p m)) White \<and>
       exactly_one_king (position_board (apply_move p m)) Black"
    using legal_move_preserves_king_count[OF hp hm] by blast
  have hno: "\<not> pawn_on_promotion_rank (position_board p)"
    using hp by (simp add: position_invariant_def)
  have hpawn:
      "\<not> pawn_on_promotion_rank (position_board (apply_move p m))"
    using pseudo_legal_preserves_pawn_rank[OF legal_move_pseudo[OF hm] hno]
    by (simp add: apply_move_board)
  have hfull: "position_fullmove (apply_move p m) > 0"
    using legal_move_preserves_fullmove_positive[OF hp hm] .
  show ?thesis using hking hpawn hfull by blast
qed

lemma legal_move_preserves_position_invariant:
  assumes hp: "position_invariant p"
    and hm: "legal_move p m"
  shows "position_invariant (apply_move p m)"
proof -
  have hcore:
      "exactly_one_king (position_board (apply_move p m)) White \<and>
       exactly_one_king (position_board (apply_move p m)) Black \<and>
       \<not> pawn_on_promotion_rank (position_board (apply_move p m)) \<and>
       position_fullmove (apply_move p m) > 0"
    using legal_move_preserves_core_position_invariant[OF hp hm] .
  have hrights: "rights_consistent (apply_move p m)"
    using legal_move_preserves_rights_consistent[OF hp hm] .
  show ?thesis
    using hcore hrights by (simp add: position_invariant_def)
qed

end
