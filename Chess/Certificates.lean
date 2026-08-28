import Chess.Mate

/-!
# Finite mate certificates

A certificate is a finite proof tree: the attacking side chooses one move,
while the defending side records a reply certificate for every legal reply.
The executable checker excludes automatic terminal draws; the logical checker
also retains the exact dead-position predicate.
-/

namespace Chess

inductive MateCertificate where
  | mateTerminal
  | mateAttacker (move : Move) (certificate : MateCertificate)
  | mateDefender (replies : List (Move × MateCertificate))

def certificateRepliesB (p : Position)
    (xs : List (Move × MateCertificate)) : Bool :=
  (legalMoves p).all (fun m => xs.any (fun x => x.1 == m))

def certificateReplies (p : Position)
    (xs : List (Move × MateCertificate)) : Prop :=
  ∀ m, m ∈ legalMoves p → ∃ x ∈ xs, x.1 = m

theorem certificateReplies_legal {p : Position}
    {xs : List (Move × MateCertificate)}
    (h : certificateReplies p xs) {m : Move} (hm : m ∈ legalMoves p) :
    ∃ x ∈ xs, x.1 = m := h m hm

def checkMateCertificateB (c : Color) (p : Position) : Nat → MateCertificate → Bool
  | _, .mateTerminal => checkmateB p && (p.turn == Color.opposite c)
  | 0, .mateAttacker _ _ => false
  | 0, .mateDefender _ => false
  | n + 1, .mateAttacker m cert =>
      (p.turn == c) && (!stalemateB p) && (!fivefoldRepetitionB [p]) &&
        (p.halfmove < 150) && legalMoveB p m &&
          checkMateCertificateB c (applyMove p m) n cert
  | n + 1, .mateDefender xs =>
      (p.turn != c) && (!stalemateB p) && (!fivefoldRepetitionB [p]) &&
        (p.halfmove < 150) && certificateRepliesB p xs &&
          xs.all (fun x =>
            legalMoveB p x.1 &&
              checkMateCertificateB c (applyMove p x.1) n x.2)

def checkMateCertificatePosition (c : Color) (p : Position)
    (n : Nat) (cert : MateCertificate) : Prop :=
  match n, cert with
  | _, .mateTerminal => checkmate p ∧ p.turn = Color.opposite c
  | 0, .mateAttacker _ _ => False
  | 0, .mateDefender _ => False
  | n + 1, .mateAttacker m child =>
      p.turn = c ∧ ¬ stalemate p ∧ ¬ deadPosition p ∧
        ¬ fivefoldRepetition [p] ∧ 150 > p.halfmove ∧ legalMove p m ∧
          checkMateCertificatePosition c (applyMove p m) n child
  | n + 1, .mateDefender xs =>
      p.turn ≠ c ∧ ¬ stalemate p ∧ ¬ deadPosition p ∧
        ¬ fivefoldRepetition [p] ∧ 150 > p.halfmove ∧ certificateReplies p xs ∧
          ∀ x ∈ xs, legalMove p x.1 ∧
            checkMateCertificatePosition c (applyMove p x.1) n x.2

noncomputable def checkMateCertificatePolicy (c : Color)
    (terminal : List Position → Prop)
    (claimCurrent : List Position → Prop)
    (claimAfter : List Position → Move → Prop)
    (hs : List Position) : Nat → MateCertificate → Prop
  | _, .mateTerminal => by
      classical
      exact match historyCurrent hs with
      | none => False
      | some p => checkmate p ∧ p.turn = Color.opposite c
  | 0, .mateAttacker _ _ => False
  | 0, .mateDefender _ => False
  | n + 1, .mateAttacker m child => by
      classical
      exact match historyCurrent hs with
      | none => False
      | some p =>
          p.turn = c ∧ ¬ stalemate p ∧ ¬ terminal hs ∧ legalMove p m ∧
            checkMateCertificatePolicy c terminal claimCurrent claimAfter
              (hs ++ [applyMove p m]) n child
  | n + 1, .mateDefender xs => by
      classical
      exact match historyCurrent hs with
      | none => False
      | some p =>
          p.turn ≠ c ∧ ¬ stalemate p ∧ ¬ terminal hs ∧ ¬ claimCurrent hs ∧
            certificateReplies p xs ∧
            ∀ x ∈ xs, legalMove p x.1 ∧ ¬ claimAfter hs x.1 ∧
              checkMateCertificatePolicy c terminal claimCurrent claimAfter
                (hs ++ [applyMove p x.1]) n x.2

def checkMateCertificateHistory (c : Color) (hs : List Position)
    (n : Nat) (cert : MateCertificate) : Prop :=
  checkMateCertificatePolicy c semanticMateTerminal semanticMateClaimCurrent
    semanticMateClaimAfter hs n cert

def checkMateCertificatePolicyB (c : Color)
    (terminal : List Position → Bool)
    (claimCurrent : List Position → Bool)
    (claimAfter : List Position → Move → Bool)
    (hs : List Position) : Nat → MateCertificate → Bool
  | _, .mateTerminal =>
      match historyCurrent hs with
      | none => false
      | some p => checkmateB p && (p.turn == Color.opposite c)
  | 0, .mateAttacker _ _ => false
  | 0, .mateDefender _ => false
  | n + 1, .mateAttacker m child =>
      match historyCurrent hs with
      | none => false
      | some p =>
          (p.turn == c) && (!stalemateB p) && (!terminal hs) && legalMoveB p m &&
            checkMateCertificatePolicyB c terminal claimCurrent claimAfter
              (hs ++ [applyMove p m]) n child
  | n + 1, .mateDefender xs =>
      match historyCurrent hs with
      | none => false
      | some p =>
          (p.turn != c) && (!stalemateB p) && (!terminal hs) &&
            (!claimCurrent hs) && certificateRepliesB p xs &&
            xs.all (fun x =>
              legalMoveB p x.1 && (!claimAfter hs x.1) &&
                checkMateCertificatePolicyB c terminal claimCurrent claimAfter
                  (hs ++ [applyMove p x.1]) n x.2)

def checkMateCertificateExecutable (c : Color) (hs : List Position)
    (n : Nat) (cert : MateCertificate) : Bool :=
  checkMateCertificatePolicyB c executableMateTerminalB executableMateClaimCurrentB
    executableMateClaimAfterB hs n cert

end Chess
