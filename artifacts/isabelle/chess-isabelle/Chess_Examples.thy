section \<open>Executable regression examples\<close>

theory Chess_Examples
  imports Chess_Symmetry Chess_Certificates Chess_SAN Chess_FEN_Text
begin

lemma initial_position_invariant:
  "position_invariant initial_position"
  by (simp add: position_invariant_def initial_position_def
      exactly_one_king_def has_piece_def all_squares_def all_files_def
      all_ranks_def pawn_on_promotion_rank_def rights_consistent_def
      filter_nonempty_iff)

lemma initial_position_legal_moves_20:
  "length (legal_moves initial_position) = 20"
  by eval

lemma initial_position_not_in_check:
  "\<not> in_check initial_position White \<and>
   \<not> in_check initial_position Black"
  by eval

lemma initial_position_not_terminal:
  "\<not> checkmate initial_position \<and> \<not> stalemate initial_position"
  by eval

lemma initial_position_perft:
  "perft initial_position 1 = 20"
  by eval

lemma initial_position_perft_2:
  "perft initial_position 2 = 400"
  by eval

lemma initial_position_perft_3:
  "perft initial_position 3 = 8902"
  by eval

lemma initial_position_perft_4:
  "perft initial_position 4 = 197281"
  by eval

lemma initial_position_perft_all:
  "perft initial_position 1 = 20 \<and>
   perft initial_position 2 = 400 \<and>
   perft initial_position 3 = 8902 \<and>
   perft initial_position 4 = 197281"
  by (simp only: initial_position_perft initial_position_perft_2
      initial_position_perft_3 initial_position_perft_4)

definition kiwipete_position :: position where
  "kiwipete_position = the (parse_fen
    ''r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1'')"

lemma kiwipete_defined:
  "parse_fen
    ''r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1''
    \<noteq> None"
  by eval

lemma kiwipete_perft_1:
  "perft kiwipete_position 1 = 48"
  by eval

lemma kiwipete_perft_2:
  "perft kiwipete_position 2 = 2039"
  by eval

lemma kiwipete_perft_3:
  "perft kiwipete_position 3 = 97862"
  by eval

definition perft_position_three :: position where
  "perft_position_three = the (parse_fen
    ''8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1'')"

lemma perft_position_three_defined:
  "parse_fen
    ''8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1''
    \<noteq> None"
  by eval

lemma perft_position_three_1:
  "perft perft_position_three 1 = 14"
  by eval

lemma perft_position_three_2:
  "perft perft_position_three 2 = 191"
  by eval

lemma perft_position_three_3:
  "perft perft_position_three 3 = 2812"
  by eval

lemma textual_fen_initial_defined:
  "parse_fen
    ''rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1'' \<noteq> None"
  by eval

lemma textual_fen_print_defined:
  "parse_fen (print_fen initial_position) \<noteq> None"
  by (simp add: print_fen_initial textual_fen_initial_defined)

lemma textual_fen_roundtrip_initial:
  "parse_fen (print_fen initial_position) \<noteq> None"
  by (rule parse_fen_print_fen)

lemma san_initial_e4:
  "print_san initial_position (Normal (E,R2) (E,R4)) = ''e4''"
  by eval

lemma san_initial_e4_parse:
  "parse_san_move initial_position ''e4'' =
     Some (Normal (E,R2) (E,R4))"
  by eval

lemma san_initial_unique:
  "san_unique_on_legal_moves initial_position"
  by eval

lemma parse_print_san_initial:
  "\<forall>m \<in> set (legal_moves initial_position).
     parse_san_move initial_position
       (print_san initial_position m) = Some m"
proof
  fix m
  assume hm: "m \<in> set (legal_moves initial_position)"
  have hlegal: "legal_move initial_position m"
    using legal_moves_correct hm by blast
  show "parse_san_move initial_position
      (print_san initial_position m) = Some m"
    using parse_print_san_legal_move_checked[OF san_initial_unique hlegal] .
qed

lemma san_kiwipete_unique:
  "san_unique_on_legal_moves kiwipete_position"
  by eval

lemma parse_print_san_kiwipete:
  "\<forall>m \<in> set (legal_moves kiwipete_position).
     parse_san_move kiwipete_position
       (print_san kiwipete_position m) = Some m"
proof
  fix m
  assume hm: "m \<in> set (legal_moves kiwipete_position)"
  have hlegal: "legal_move kiwipete_position m"
    using legal_moves_correct hm by blast
  show "parse_san_move kiwipete_position
      (print_san kiwipete_position m) = Some m"
    using parse_print_san_legal_move_checked[OF san_kiwipete_unique hlegal] .
qed

lemma uci_initial_e4:
  "print_uci_text initial_position (Normal (E,R2) (E,R4)) = ''e2e4''"
  by eval

lemma uci_initial_e4_parse:
  "parse_uci_text initial_position ''e2e4'' =
     Some (Normal (E,R2) (E,R4))"
  by eval

lemma uci_initial_e4_roundtrip:
  "parse_uci_text initial_position
      (print_uci_text initial_position (Normal (E,R2) (E,R4))) =
     Some (Normal (E,R2) (E,R4))"
  by eval

definition castle_example :: position where
  "castle_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (H,R1) then Some \<lparr>piece_color = White, piece_kind = Rook\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {WhiteKingSide},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma castle_example_legal:
  "legal_move castle_example WhiteKingCastle"
  by eval

lemma uci_castle_example:
  "print_uci_text castle_example WhiteKingCastle = ''e1g1'' \<and>
   parse_uci_text castle_example ''e1g1'' = Some WhiteKingCastle"
  by eval

lemma castle_example_destination:
  "position_board (apply_move castle_example WhiteKingCastle) (G,R1) =
     Some \<lparr>piece_color = White, piece_kind = King\<rparr>"
  by eval

definition en_passant_example :: position where
  "en_passant_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (E,R5) then Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>
       else if s = (D,R5) then Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = Some (D,R6),
     position_halfmove = 0,
     position_fullmove = 2\<rparr>"

lemma en_passant_example_legal:
  "legal_move en_passant_example (EnPassant (E,R5) (D,R6))"
  by eval

lemma en_passant_example_captured:
  "position_board (apply_move en_passant_example (EnPassant (E,R5) (D,R6))) (D,R5) = None"
  by eval

definition promotion_example :: position where
  "promotion_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (A,R7) then Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma promotion_example_legal:
  "legal_move promotion_example (Promotion (A,R7) (A,R8) PromoteQueen)"
  by eval

lemma uci_promotion_example:
  "print_uci_text promotion_example
      (Promotion (A,R7) (A,R8) PromoteQueen) = ''a7a8q'' \<and>
   parse_uci_text promotion_example ''a7a8q'' =
      Some (Promotion (A,R7) (A,R8) PromoteQueen)"
  by eval

lemma promotion_example_piece:
  "position_board (apply_move promotion_example
      (Promotion (A,R7) (A,R8) PromoteQueen)) (A,R8) =
     Some \<lparr>piece_color = White, piece_kind = Queen\<rparr>"
  by eval

definition mate_one_example :: position where
  "mate_one_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (F,R7) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (G,R7) then Some \<lparr>piece_color = White, piece_kind = Queen\<rparr>
       else if s = (H,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma mate_one_example_move:
  "legal_move mate_one_example (Normal (G,R7) (G,R8))"
  by eval

lemma mate_one_example_checkmate:
  "checkmate (apply_move mate_one_example (Normal (G,R7) (G,R8)))"
  by eval

lemma mate_one_example_certificate:
  "forced_mate_within White mate_one_example 1"
proof -
  have hnotcheck: "\<not> checkmate mate_one_example"
    by eval
  have hstalemate: "\<not> stalemate mate_one_example"
    by eval
  have hdead: "\<not> dead_position mate_one_example"
  proof -
    have hcur: "current_mate
        (apply_move mate_one_example (Normal (G,R7) (G,R8)))"
      using mate_one_example_checkmate
      by (simp add: current_mate_def checkmate_def)
    show ?thesis
      using legal_move_child_current_mate_not_dead
        mate_one_example_move hcur by blast
  qed
  have h75: "\<not> seventy_five_move_draw mate_one_example"
    by eval
  have hturn: "position_turn mate_one_example = White"
    by (simp add: mate_one_example_def)
  have hm: "Normal (G,R7) (G,R8) \<in> set (legal_moves mate_one_example)"
    using mate_one_example_move legal_moves_complete by blast
  have hchild: "forced_mate_within White
      (apply_move mate_one_example (Normal (G,R7) (G,R8))) 0"
  proof -
    have hmate:
        "checkmate (apply_move mate_one_example (Normal (G,R7) (G,R8)))"
      using mate_one_example_checkmate .
    have hchildturn:
        "position_turn (apply_move mate_one_example
          (Normal (G,R7) (G,R8))) = opponent White"
      using turn_apply_move hturn by simp
    show ?thesis
      using hmate hchildturn by (simp add: forced_mate_zero)
  qed
  have hex:
      "list_ex (\<lambda>m. forced_mate_within White
          (apply_move mate_one_example m) 0)
        (legal_moves mate_one_example)"
    using hm hchild by (auto simp add: list_ex_iff)
  show ?thesis
    using hnotcheck hstalemate hdead h75 hturn hex
    by (simp add: forced_mate_within_def fivefold_singleton_false)
qed

lemma mate_one_example_history_certificate:
  "check_mate_certificate_history White [mate_one_example] 1
    (MateAttacker (Normal (G,R7) (G,R8)) MateTerminal)"
proof -
  have hdead: "\<not> dead_position mate_one_example"
  proof -
    have hcur: "current_mate
        (apply_move mate_one_example (Normal (G,R7) (G,R8)))"
      using mate_one_example_checkmate
      by (simp add: current_mate_def checkmate_def)
    show ?thesis
      using legal_move_child_current_mate_not_dead
        mate_one_example_move hcur by blast
  qed
  have h75: "\<not> seventy_five_move_draw mate_one_example"
    by eval
  have hterminal: "\<not> semantic_mate_terminal [mate_one_example]"
    using hdead h75
    by (simp add: semantic_mate_terminal_def history_current_def
      fivefold_singleton_false)
  have hturn: "position_turn mate_one_example = White"
    by (simp add: mate_one_example_def)
  have hchildturn:
      "position_turn (apply_move mate_one_example
        (Normal (G,R7) (G,R8))) = opponent White"
    using turn_apply_move hturn by simp
  have hm: "legal_move mate_one_example (Normal (G,R7) (G,R8))"
    using mate_one_example_move .
  have hm': "Normal (G,R7) (G,R8) \<in> set (legal_moves mate_one_example)"
    using legal_moves_complete[OF hm] .
  have hstalemate: "\<not> stalemate mate_one_example"
    using hm' by (auto simp add: stalemate_def)
  show ?thesis
    unfolding check_mate_certificate_history_def
    using mate_one_example_checkmate hchildturn hm hterminal hturn hstalemate
    by (simp add: check_mate_certificate_policy.simps history_current_def)
qed

definition stalemate_example :: position where
  "stalemate_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (F,R7) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (G,R6) then Some \<lparr>piece_color = White, piece_kind = Queen\<rparr>
       else if s = (H,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = Black,
     position_castling = {},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma stalemate_example_stalemate:
  "stalemate stalemate_example"
  by eval

definition castle_through_check_example :: position where
  "castle_through_check_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (H,R1) then Some \<lparr>piece_color = White, piece_kind = Rook\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else if s = (F,R8) then Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>
       else None),
     position_turn = White,
     position_castling = {WhiteKingSide},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma castle_through_check_rejected:
  "pseudo_legal castle_through_check_example WhiteKingCastle \<and>
   \<not> legal_move castle_through_check_example WhiteKingCastle"
  by eval

definition en_passant_discovered_check_example :: position where
  "en_passant_discovered_check_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (E,R5) then Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>
       else if s = (D,R5) then Some \<lparr>piece_color = Black, piece_kind = Pawn\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = Rook\<rparr>
       else if s = (A,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = Some (D,R6),
     position_halfmove = 0,
     position_fullmove = 2\<rparr>"

lemma en_passant_discovered_check_rejected:
  "pseudo_legal en_passant_discovered_check_example (EnPassant (E,R5) (D,R6)) \<and>
   \<not> legal_move en_passant_discovered_check_example (EnPassant (E,R5) (D,R6))"
  by eval

definition promotion_mate_example :: position where
  "promotion_mate_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (F,R7) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (G,R7) then Some \<lparr>piece_color = White, piece_kind = Pawn\<rparr>
       else if s = (H,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma promotion_mate_example_checkmate:
  "legal_move promotion_mate_example (Promotion (G,R7) (G,R8) PromoteQueen) \<and>
   checkmate (apply_move promotion_mate_example
      (Promotion (G,R7) (G,R8) PromoteQueen))"
  by eval

definition san_disambiguation_example :: position where
  "san_disambiguation_example =
    \<lparr>position_board = (\<lambda>s.
       if s = (E,R1) then Some \<lparr>piece_color = White, piece_kind = King\<rparr>
       else if s = (D,R2) then Some \<lparr>piece_color = White, piece_kind = Knight\<rparr>
       else if s = (H,R2) then Some \<lparr>piece_color = White, piece_kind = Knight\<rparr>
       else if s = (E,R8) then Some \<lparr>piece_color = Black, piece_kind = King\<rparr>
       else None),
     position_turn = White,
     position_castling = {},
     position_en_passant = None,
     position_halfmove = 0,
     position_fullmove = 1\<rparr>"

lemma san_disambiguation_example:
  "print_san san_disambiguation_example (Normal (D,R2) (F,R3)) = ''Ndf3'' \<and>
   print_san san_disambiguation_example (Normal (H,R2) (F,R3)) = ''Nhf3''"
  by eval

definition fifty_move_clock_example :: position where
  "fifty_move_clock_example =
    initial_position\<lparr>position_halfmove := 100\<rparr>"

definition fifty_move_intended_example :: position where
  "fifty_move_intended_example =
    initial_position\<lparr>position_halfmove := 99\<rparr>"

definition seventy_five_move_clock_example :: position where
  "seventy_five_move_clock_example =
    initial_position\<lparr>position_halfmove := 150\<rparr>"

lemma fifty_move_clock_example_claimable:
  "fifty_move_claimable fifty_move_clock_example"
  by (simp add: fifty_move_clock_example_def fifty_move_claimable_def)

lemma fifty_move_intended_claimable:
  "fifty_move_claimable_after fifty_move_intended_example
     (Normal (B,R1) (C,R3))"
  by eval

lemma seventy_five_move_clock_example_draw:
  "seventy_five_move_draw seventy_five_move_clock_example"
  by (simp add: seventy_five_move_clock_example_def seventy_five_move_draw_def)

lemma fivefold_repetition_example:
  "fivefold_repetition
      [initial_position, initial_position, initial_position,
       initial_position, initial_position]"
  by (simp add: fivefold_repetition_def key_occurrences_def)

lemma fen_roundtrip_example:
  "parse_fen_fields (print_fen_fields initial_position) = Some initial_position"
  by (rule parse_fen_fields_print_fen_fields)

lemma example_suite_correct:
  "length (legal_moves initial_position) = 20 \<and>
   perft initial_position 1 = 20 \<and>
   perft initial_position 2 = 400 \<and>
   perft initial_position 3 = 8902 \<and>
   perft initial_position 4 = 197281 \<and>
   parse_fen
      ''r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1''
      \<noteq> None \<and>
   perft kiwipete_position 1 = 48 \<and>
   perft kiwipete_position 2 = 2039 \<and>
   perft kiwipete_position 3 = 97862 \<and>
   parse_fen
      ''8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1''
      \<noteq> None \<and>
   perft perft_position_three 1 = 14 \<and>
   perft perft_position_three 2 = 191 \<and>
   perft perft_position_three 3 = 2812 \<and>
   parse_fen_fields (print_fen_fields initial_position) = Some initial_position \<and>
   parse_fen (print_fen initial_position) \<noteq> None \<and>
   san_unique_on_legal_moves initial_position \<and>
   san_unique_on_legal_moves kiwipete_position \<and>
   print_san initial_position (Normal (E,R2) (E,R4)) = ''e4'' \<and>
   print_uci_text initial_position (Normal (E,R2) (E,R4)) = ''e2e4'' \<and>
   parse_uci_text initial_position ''e2e4'' =
      Some (Normal (E,R2) (E,R4)) \<and>
   legal_move castle_example WhiteKingCastle \<and>
   print_uci_text castle_example WhiteKingCastle = ''e1g1'' \<and>
   parse_uci_text castle_example ''e1g1'' = Some WhiteKingCastle \<and>
   legal_move en_passant_example (EnPassant (E,R5) (D,R6)) \<and>
   legal_move promotion_example (Promotion (A,R7) (A,R8) PromoteQueen) \<and>
   print_uci_text promotion_example
      (Promotion (A,R7) (A,R8) PromoteQueen) = ''a7a8q'' \<and>
   parse_uci_text promotion_example ''a7a8q'' =
      Some (Promotion (A,R7) (A,R8) PromoteQueen) \<and>
   forced_mate_within White mate_one_example 1 \<and>
   check_mate_certificate_history White [mate_one_example] 1
      (MateAttacker (Normal (G,R7) (G,R8)) MateTerminal) \<and>
   stalemate stalemate_example \<and>
   \<not> legal_move castle_through_check_example WhiteKingCastle \<and>
   \<not> legal_move en_passant_discovered_check_example
      (EnPassant (E,R5) (D,R6)) \<and>
   checkmate (apply_move promotion_mate_example
      (Promotion (G,R7) (G,R8) PromoteQueen)) \<and>
   fifty_move_claimable fifty_move_clock_example \<and>
   seventy_five_move_draw seventy_five_move_clock_example \<and>
   fivefold_repetition
      [initial_position, initial_position, initial_position,
       initial_position, initial_position]"
  by (simp only: initial_position_legal_moves_20 initial_position_perft
      initial_position_perft_2 initial_position_perft_3 initial_position_perft_4
      kiwipete_defined kiwipete_perft_1 kiwipete_perft_2 kiwipete_perft_3
      perft_position_three_defined perft_position_three_1
      perft_position_three_2 perft_position_three_3
      fen_roundtrip_example textual_fen_roundtrip_initial san_initial_unique
      san_kiwipete_unique san_initial_e4
      uci_initial_e4 uci_initial_e4_parse uci_castle_example
      uci_promotion_example castle_example_legal en_passant_example_legal
      promotion_example_legal
      mate_one_example_certificate mate_one_example_history_certificate
      stalemate_example_stalemate
      castle_through_check_rejected en_passant_discovered_check_rejected
      promotion_mate_example_checkmate fifty_move_clock_example_claimable
      seventy_five_move_clock_example_draw fivefold_repetition_example; simp)

end
