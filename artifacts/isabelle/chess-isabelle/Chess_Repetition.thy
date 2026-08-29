section \<open>Repetition identity and claims\<close>

theory Chess_Repetition
  imports Chess_History
begin

record repetition_key =
  rep_board :: board
  rep_turn :: color
  rep_castling :: castling_rights
  rep_en_passant :: "square option"

definition legal_en_passant_available :: "position \<Rightarrow> bool" where
  "legal_en_passant_available p \<longleftrightarrow>
    (\<exists>m. legal_move p m \<and> is_en_passant m)"

definition effective_en_passant :: "position \<Rightarrow> square option" where
  "effective_en_passant p =
    (if legal_en_passant_available p
     then position_en_passant p else None)"

definition repetition_key :: "position \<Rightarrow> repetition_key" where
  "repetition_key p =
    \<lparr>rep_board = position_board p,
     rep_turn = position_turn p,
     rep_castling = position_castling p,
     rep_en_passant = effective_en_passant p\<rparr>"

definition key_occurrences :: "repetition_key \<Rightarrow> position list \<Rightarrow> nat" where
  "key_occurrences k hs =
    length (filter (\<lambda>p. repetition_key p = k) hs)"

definition threefold_claimable :: "position list \<Rightarrow> bool" where
  "threefold_claimable hs \<longleftrightarrow>
    (case rev hs of
       [] \<Rightarrow> False
     | p#ps \<Rightarrow> key_occurrences (repetition_key p) hs \<ge> 3)"

definition fivefold_repetition :: "position list \<Rightarrow> bool" where
  "fivefold_repetition hs \<longleftrightarrow>
    (case rev hs of
       [] \<Rightarrow> False
     | p#ps \<Rightarrow> key_occurrences (repetition_key p) hs \<ge> 5)"

text \<open>
  FIDE's claimable repetition rule also admits an announced legal move that
  would create the third occurrence.  The history is stored in game order;
  the candidate child is therefore appended before its key is counted.
\<close>

definition threefold_claimable_after :: "position list \<Rightarrow> move \<Rightarrow> bool" where
  "threefold_claimable_after hs m \<longleftrightarrow>
    (case rev hs of
       [] \<Rightarrow> False
     | p#ps \<Rightarrow>
         legal_move p m \<and>
         key_occurrences (repetition_key (apply_move p m))
           (hs @ [apply_move p m]) \<ge> 3)"

definition fifty_move_claimable_after :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "fifty_move_claimable_after p m \<longleftrightarrow>
    legal_move p m \<and> position_halfmove (apply_move p m) \<ge> 100"

lemma fifty_move_claimable_after_iff:
  "fifty_move_claimable_after p m \<longleftrightarrow>
     legal_move p m \<and> position_halfmove (apply_move p m) \<ge> 100"
  by (simp add: fifty_move_claimable_after_def)

lemma same_repetition_position_iff:
  "repetition_key p = repetition_key q \<longleftrightarrow>
     position_board p = position_board q \<and>
     position_turn p = position_turn q \<and>
     position_castling p = position_castling q \<and>
     effective_en_passant p = effective_en_passant q"
  by (simp add: repetition_key_def)

lemma clocks_irrelevant_to_repetition:
  "position_board p = position_board q \<Longrightarrow>
   position_turn p = position_turn q \<Longrightarrow>
   position_castling p = position_castling q \<Longrightarrow>
   effective_en_passant p = effective_en_passant q \<Longrightarrow>
   repetition_key p = repetition_key q"
  by (simp add: repetition_key_def)

end
