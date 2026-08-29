section \<open>Promotion prerequisites\<close>

theory Chess_Promotion
  imports Chess_Geometry Chess_Move
begin

definition promotion_rank :: "color \<Rightarrow> rank" where
  "promotion_rank c = (if c = White then R8 else R1)"

definition pseudo_legal_promotion :: "position \<Rightarrow> move \<Rightarrow> bool" where
  "pseudo_legal_promotion p m \<longleftrightarrow>
    (case m of
       Promotion s t k \<Rightarrow>
         (case position_board p s of
            Some q \<Rightarrow>
              piece_color q = position_turn p \<and>
              piece_kind q = Pawn \<and>
              snd t = promotion_rank (position_turn p) \<and>
              ((pawn_move_geometry (position_turn p) s t \<and>
                 position_board p t = None) \<or>
               (pawn_attack_geometry (position_turn p) s t \<and>
                (case position_board p t of
                    Some q' \<Rightarrow>
                      piece_color q' = opponent (position_turn p) \<and>
                      piece_kind q' \<noteq> King
                  | None \<Rightarrow> False)))
          | None \<Rightarrow> False)
     | _ \<Rightarrow> False)"

lemma promotion_kind_allowed:
  "promotion_piece_kind k \<in> {Queen, Rook, Bishop, Knight}"
  by (cases k; simp)

lemma legal_promotion_kind:
  "promotion_piece_kind k \<in> {Queen, Rook, Bishop, Knight}"
  by (rule promotion_kind_allowed)

lemma promotion_rank_cases:
  "promotion_rank White = R8" "promotion_rank Black = R1"
  by (simp_all add: promotion_rank_def)

end
