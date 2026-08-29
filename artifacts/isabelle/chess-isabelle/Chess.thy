section \<open>Verified executable chess kernel\<close>

theory Chess
  imports Chess_Examples
begin

text \<open>
  The capstone inventory records the semantic and interoperability results
  that are easy to miss when reading only the exported code: the exhaustive
  finite-generator refinement, preservation of the structural invariant and
  its reachability lifting, textual FEN and UCI round trips, unconditional SAN
  injectivity and parsing, history-aware certificate soundness/completeness,
  and the legal/checkmate/stalemate symmetry transport.  The executable
  terminal policy remains parameterized: the semantic policy contains the
  exact unbounded dead-position predicate, while generated code accepts a
  caller-supplied terminal predicate.
\<close>

lemma chess_kernel_correct:
  "(\<forall>p m. m \<in> set (legal_moves p) \<longleftrightarrow> legal_move p m) \<and>
   (\<forall>p m. position_invariant p \<longrightarrow> legal_move p m \<longrightarrow>
      position_invariant (apply_move p m)) \<and>
   (\<forall>p. reachable p \<longrightarrow> position_invariant p) \<and>
   (\<forall>p. parse_fen_fields (print_fen_fields p) = Some p) \<and>
   (\<forall>p. position_fullmove p > 0 \<longrightarrow>
      parse_fen (print_fen p) = Some p) \<and>
   (\<forall>p m. legal_move p m \<longrightarrow>
      parse_uci_text p (print_uci_text p m) = Some m) \<and>
   (\<forall>p m. legal_move p m \<longrightarrow>
      parse_uci_move p (print_uci_move p m) = Some m) \<and>
   (\<forall>p m n. legal_move p m \<longrightarrow> legal_move p n \<longrightarrow>
      print_san p m = print_san p n \<longrightarrow> m = n) \<and>
   (\<forall>p m. legal_move p m \<longrightarrow>
      parse_san_move p (print_san p m) = Some m) \<and>
   (\<forall>c hs n cert. check_mate_certificate_history c hs n cert \<longrightarrow>
      forced_mate_within_history c hs n) \<and>
   (\<forall>c hs n. forced_mate_within_history c hs n \<longrightarrow>
      (\<exists>cert. check_mate_certificate_history c hs n cert)) \<and>
   (\<forall>p. perft p 0 = 1) \<and>
   (\<forall>c hs n. mate_in c hs n \<longleftrightarrow>
      forced_mate_within_history c hs n) \<and>
   (\<forall>p m. position_invariant p \<longrightarrow>
      (legal_move (mirror_position p) (mirror_move m) \<longleftrightarrow>
       legal_move p m)) \<and>
   (\<forall>p. position_invariant p \<longrightarrow>
      ((checkmate (mirror_position p) \<longleftrightarrow> checkmate p) \<and>
       (stalemate (mirror_position p) \<longleftrightarrow> stalemate p)))"
  by (simp add: legal_moves_correct legal_move_preserves_position_invariant
      reachable_position_invariant parse_fen_fields_print_fen_fields
      parse_fen_print_fen_position parse_print_uci_text_legal_move
      parse_print_uci_legal_move_unique
      print_san_injective_legal parse_print_san_legal_move_unconditional
      check_mate_certificate_history_sound forced_mate_history_has_certificate
      perft_zero mate_in_history_correct legal_move_mirror checkmate_mirror
      stalemate_mirror)

export_code parse_fen print_fen parse_fen_fields print_fen_fields
  legal_moves apply_move checkmate stalemate
  uci_of_move parse_uci_move parse_uci_text print_uci_text
  print_san parse_san_move
  perft forced_mate_within_policy forced_mate_within_terminal
  in SML module_name Chess_Kernel

end
