import Chess.Certificates
import Chess.FENText

/-!
# The Isabelle mate-in-two showcase

This is the concrete certificate from `Chess_Mate_Two.thy`.  The statement is
kept as data plus executable checks: the key move is followed by a complete
finite list of Black replies, and every reply is answered by a certified mate.
-/

namespace Chess

def mateTwoCandidate : Position :=
  Option.getD
    (parseFen "kr6/1r1N4/2Q5/8/8/8/8/K7 w - - 0 1")
    initialPosition

def mateTwoKeyMove : Move :=
  .normal (⟨3, by decide⟩, ⟨6, by decide⟩)
    (⟨2, by decide⟩, ⟨4, by decide⟩)

def mateTwoKeyPosition : Position := applyMove mateTwoCandidate mateTwoKeyMove

def mateTwoKingReply : Move :=
  .normal (⟨0, by decide⟩, ⟨7, by decide⟩)
    (⟨0, by decide⟩, ⟨6, by decide⟩)

def mateTwoKingMate : Move :=
  .normal (⟨2, by decide⟩, ⟨5, by decide⟩)
    (⟨0, by decide⟩, ⟨5, by decide⟩)

def mateTwoRookReplies : List Move :=
  [ .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨2, by decide⟩, ⟨7, by decide⟩)
  , .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨3, by decide⟩, ⟨7, by decide⟩)
  , .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨4, by decide⟩, ⟨7, by decide⟩)
  , .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨5, by decide⟩, ⟨7, by decide⟩)
  , .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨6, by decide⟩, ⟨7, by decide⟩)
  , .normal (⟨1, by decide⟩, ⟨7, by decide⟩) (⟨7, by decide⟩, ⟨7, by decide⟩) ]

def mateTwoRookMate : Move :=
  .normal (⟨2, by decide⟩, ⟨5, by decide⟩)
    (⟨1, by decide⟩, ⟨6, by decide⟩)

def mateTwoExpectedReplies : List Move := mateTwoKingReply :: mateTwoRookReplies

def mateTwoCertificate : MateCertificate :=
  .mateAttacker mateTwoKeyMove
    (.mateDefender
      ((mateTwoKingReply, .mateAttacker mateTwoKingMate .mateTerminal) ::
        mateTwoRookReplies.map (fun reply =>
          (reply, .mateAttacker mateTwoRookMate .mateTerminal))))

theorem mateTwoCandidate_defined :
    (parseFen "kr6/1r1N4/2Q5/8/8/8/8/K7 w - - 0 1").isSome = true := by
  native_decide

theorem mateTwoKeyMove_legal : legalMoveB mateTwoCandidate mateTwoKeyMove = true := by
  native_decide

theorem mateTwoKeyReplies_exact :
    legalMoves mateTwoKeyPosition = mateTwoExpectedReplies := by
  native_decide

theorem mateTwoCertificate_checked :
    checkMateCertificateB .white mateTwoCandidate 3 mateTwoCertificate = true := by
  native_decide

theorem mateTwoCertificate_history_checked :
    checkMateCertificateExecutable .white [mateTwoCandidate] 3 mateTwoCertificate = true := by
  native_decide

theorem mateTwoCertificate_rules_checked :
    ruleCertificateCheckB (fun _ => false) .white mateTwoCandidate 3
      mateTwoCertificate = true := by
  native_decide

theorem mateTwoCertificate_rules_forced :
    ruleForcedMate (fun _ => false) .white mateTwoCandidate 3 := by
  apply (mateCertificate_rules_adequate (fun _ => false) .white
    mateTwoCandidate 3).1
  exact ⟨mateTwoCertificate, mateTwoCertificate_rules_checked⟩

theorem mateTwoKingLine_checkmate :
    checkmateB (applyMove (applyMove mateTwoKeyPosition mateTwoKingReply)
      mateTwoKingMate) = true := by
  native_decide

theorem mateTwoRookLines_checkmate :
    (mateTwoRookReplies.all (fun reply =>
      checkmateB (applyMove (applyMove mateTwoKeyPosition reply) mateTwoRookMate))) = true := by
  native_decide

end Chess
