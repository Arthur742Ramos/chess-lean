section \<open>En-passant prerequisites\<close>

theory Chess_En_Passant
  imports Chess_Attacks Chess_Move
begin

definition ep_captured_square :: "color \<Rightarrow> square \<Rightarrow> square option" where
  "ep_captured_square c t =
    (if c = White \<and> snd t = R6 then Some (fst t, R5)
     else if c = Black \<and> snd t = R3 then Some (fst t, R4)
     else None)"

definition pseudo_legal_en_passant :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "pseudo_legal_en_passant p m \<longleftrightarrow>
    (case m of
       EnPassant s t \<Rightarrow>
         (case position_en_passant p of
            Some ep \<Rightarrow>
              ep = t \<and>
              (case position_board p s of
                 Some q \<Rightarrow>
                   piece_color q = position_turn p \<and>
                   piece_kind q = Pawn \<and>
                   pawn_attack_geometry (position_turn p) s t \<and>
                   position_board p t = None \<and>
                   (case ep_captured_square (position_turn p) t of
                      Some cs \<Rightarrow>
                        has_piece (position_board p) cs
                          (opponent (position_turn p)) Pawn
                    | None \<Rightarrow> False)
               | None \<Rightarrow> False)
          | None \<Rightarrow> False)
     | _ \<Rightarrow> False)"

lemma ep_captured_square_rank:
  "ep_captured_square c t = Some u \<Longrightarrow>
     (c = White \<and> snd u = R5 \<and> snd t = R6) \<or>
     (c = Black \<and> snd u = R4 \<and> snd t = R3)"
  by (cases c; cases t; cases u;
      simp_all add: ep_captured_square_def split: if_splits)

end
