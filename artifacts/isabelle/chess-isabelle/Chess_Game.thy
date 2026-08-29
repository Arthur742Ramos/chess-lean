section \<open>Game status\<close>

theory Chess_Game
  imports Chess_Draws
begin

datatype game_status =
    WhiteWin
  | BlackWin
  | AutomaticDraw draw_reason
  | ClaimableDraw draw_reason
  | Ongoing

definition checkmate :: "position \<Rightarrow> bool" where
  "checkmate p \<longleftrightarrow>
    in_check p (position_turn p) \<and> legal_moves p = []"

definition stalemate :: "position \<Rightarrow> bool" where
  "stalemate p \<longleftrightarrow>
    \<not> in_check p (position_turn p) \<and> legal_moves p = []"

definition game_status :: "position list \<Rightarrow> game_status" where
  "game_status hs =
    (case rev hs of
       [] \<Rightarrow> Ongoing
     | p#ps \<Rightarrow>
         if checkmate p then
           (if position_turn p = White then BlackWin else WhiteWin)
         else if stalemate p then AutomaticDraw StalemateDraw
         else if dead_position p then AutomaticDraw DeadPositionDraw
         else if fivefold_repetition hs then AutomaticDraw RepetitionDraw
         else if seventy_five_move_draw p then AutomaticDraw SeventyFiveMoveDraw
         else if threefold_claimable hs then ClaimableDraw RepetitionDraw
         else if fifty_move_claimable p then ClaimableDraw FiftyMoveDraw
         else Ongoing)"

lemma checkmate_not_stalemate:
  "checkmate p \<Longrightarrow> \<not> stalemate p"
  by (simp add: checkmate_def stalemate_def)

end
