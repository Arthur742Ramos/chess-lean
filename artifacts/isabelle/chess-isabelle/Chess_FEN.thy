section \<open>Typed six-field FEN interchange\<close>

theory Chess_FEN
  imports Chess_Position
begin

text \<open>
  The logical interchange layer keeps the six FEN fields typed.  A concrete
  text codec can serialize this record without changing any chess semantics;
  keeping parsing typed makes malformed fields impossible in the kernel layer.
\<close>

record fen =
  fen_board :: board
  fen_turn :: color
  fen_castling :: castling_rights
  fen_en_passant :: "square option"
  fen_halfmove :: nat
  fen_fullmove :: nat

definition print_fen_fields :: "position \<Rightarrow> fen" where
  "print_fen_fields p =
    \<lparr>fen_board = position_board p,
     fen_turn = position_turn p,
     fen_castling = position_castling p,
     fen_en_passant = position_en_passant p,
     fen_halfmove = position_halfmove p,
     fen_fullmove = position_fullmove p\<rparr>"

definition parse_fen_fields :: "fen \<Rightarrow> position option" where
  "parse_fen_fields f =
    Some \<lparr>position_board = fen_board f,
      position_turn = fen_turn f,
      position_castling = fen_castling f,
      position_en_passant = fen_en_passant f,
      position_halfmove = fen_halfmove f,
      position_fullmove = fen_fullmove f\<rparr>"

definition serializable_position :: "position \<Rightarrow> bool" where
  "serializable_position p \<longleftrightarrow> position_fullmove p > 0"

lemma parse_fen_fields_print_fen_fields:
  "parse_fen_fields (print_fen_fields p) = Some p"
  by (simp add: parse_fen_fields_def print_fen_fields_def)

lemma print_fen_fields_parse_fen_fields:
  "parse_fen_fields f = Some p \<Longrightarrow> print_fen_fields p = f"
  by (auto simp add: parse_fen_fields_def print_fen_fields_def split: option.splits)

end
