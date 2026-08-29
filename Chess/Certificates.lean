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

/-!
# Adequacy of finite mate certificates

`checkMateCertificateB` is a Boolean proof checker for a finite alternating
game tree.  The following logical recurrence gives the corresponding bounded
forced-mate semantics, including the executable automatic-draw guards.  The
adequacy theorem is both soundness and completeness: a finite certificate is
accepted exactly when the attacking colour has a bounded forced mate under
this rule-level semantics.  The history-aware policy remains exposed by
`checkMateCertificateExecutable` above.
-/

noncomputable def certificateForcedMate (c : Color) (p : Position) : Nat → Prop
  | 0 => checkmateB p = true ∧ p.turn = Color.opposite c
  | n + 1 => by
      classical
      exact if checkmateB p = true then p.turn = Color.opposite c
      else if stalemateB p = true then False
      else if fivefoldRepetitionB [p] = true then False
      else if 150 ≤ p.halfmove then False
      else if p.turn = c then
        ∃ m, m ∈ legalMoves p ∧ certificateForcedMate c (applyMove p m) n
      else
        ∀ m, m ∈ legalMoves p → certificateForcedMate c (applyMove p m) n

theorem mateCertificate_sound (c : Color) (p : Position) (n : Nat)
    (cert : MateCertificate)
    (h : checkMateCertificateB c p n cert = true) :
    certificateForcedMate c p n := by
  induction n generalizing p cert with
  | zero =>
      cases cert with
      | mateTerminal =>
          simpa [checkMateCertificateB, checkmateB,
            certificateForcedMate, Bool.and_eq_true] using h
      | mateAttacker m child =>
          simp [checkMateCertificateB] at h
      | mateDefender xs =>
          simp [checkMateCertificateB] at h
  | succ n ih =>
      cases cert with
      | mateTerminal =>
          have hh : checkmateB p = true ∧
              p.turn = Color.opposite c := by
            simpa [checkMateCertificateB, Bool.and_eq_true] using h
          simp [certificateForcedMate, hh.1, hh.2]
      | mateAttacker m child =>
          have h' : p.turn = c ∧ stalemateB p = false ∧
              fivefoldRepetitionB [p] = false ∧
              decide (p.halfmove < 150) = true ∧
              legalMoveB p m = true ∧
              checkMateCertificateB c (applyMove p m) n child = true := by
            simpa only [checkMateCertificateB, Bool.and_eq_true, beq_iff_eq,
              Bool.not_eq_true_eq_eq_false, and_assoc] using h
          rcases h' with ⟨hturn, hstable, hfive, hclock, hlegal, hchild⟩
          have hlegal' : legalMove p m :=
            (legalMove_iff_legalMoveB p m).2 hlegal
          have hmem : m ∈ legalMoves p :=
            (legalMoves_correct p m).2 hlegal'
          have hcheck : checkmateB p = false := by
            by_contra hnot
            have : checkmateB p = true := Bool.eq_true_of_not_eq_false hnot
            have hparts : inCheckB p p.turn = true ∧
                (legalMoves p).isEmpty = true := by
              simpa [checkmateB] using this
            have hempty : legalMoves p = [] := by simpa using hparts.2
            simp [hempty] at hmem
          have hforced : certificateForcedMate c (applyMove p m) n :=
            ih (applyMove p m) child hchild
          have hclock' : p.halfmove < 150 := by simpa using hclock
          have hnotclock : ¬ 150 ≤ p.halfmove := by omega
          simp [certificateForcedMate, hcheck, hstable, hfive, hnotclock,
            hturn]
          exact ⟨m, hmem, hforced⟩
      | mateDefender xs =>
          have h' : p.turn ≠ c ∧ stalemateB p = false ∧
              fivefoldRepetitionB [p] = false ∧
              decide (p.halfmove < 150) = true ∧
              certificateRepliesB p xs = true ∧
              xs.all (fun x => legalMoveB p x.1 &&
                checkMateCertificateB c (applyMove p x.1) n x.2) = true := by
            simpa only [checkMateCertificateB, Bool.and_eq_true, beq_iff_eq,
              bne_iff_ne, Bool.not_eq_true_eq_eq_false, and_assoc] using h
          rcases h' with ⟨hturn, hstable, hfive, hclock, hreplies, hchildren⟩
          have hreplies' : ∀ m, m ∈ legalMoves p → ∃ x ∈ xs, x.1 = m := by
            simpa [certificateRepliesB] using hreplies
          by_cases hcheck : checkmateB p = true
          · have hmate : p.turn = Color.opposite c := by
              have hturn' : p.turn ≠ c := hturn
              cases c <;> cases ht : p.turn <;> simp_all [Color.opposite]
            simp [certificateForcedMate, hcheck, hmate]
          · have hclock' : p.halfmove < 150 := by simpa using hclock
            have hnotclock : ¬ 150 ≤ p.halfmove := by omega
            simp [certificateForcedMate, hcheck, hstable, hfive, hnotclock,
              hturn]
            intro m hm
            obtain ⟨x, hx, hxm⟩ := hreplies' m hm
            have hchild : checkMateCertificateB c (applyMove p x.1) n x.2 = true := by
              have hall := (List.all_eq_true.mp hchildren) x hx
              have hall' : legalMoveB p x.1 = true ∧
                  checkMateCertificateB c (applyMove p x.1) n x.2 = true := by
                simpa only [Bool.and_eq_true] using hall
              exact hall'.2
            simpa [hxm] using ih (applyMove p x.1) x.2 hchild

theorem mateCertificate_complete (c : Color) (p : Position) (n : Nat)
    (h : certificateForcedMate c p n) :
    ∃ cert, checkMateCertificateB c p n cert = true := by
  induction n generalizing p with
  | zero =>
      refine ⟨.mateTerminal, ?_⟩
      simpa [checkMateCertificateB, certificateForcedMate, Bool.and_eq_true] using h
  | succ n ih =>
      by_cases hcheck : checkmateB p = true
      · have hturn : p.turn = Color.opposite c := by
          simpa [certificateForcedMate, hcheck] using h
        refine ⟨.mateTerminal, ?_⟩
        simpa [checkMateCertificateB, hturn] using hcheck
      · by_cases hstable : stalemateB p = true
        · simp [certificateForcedMate, hcheck, hstable] at h
        · by_cases hfive : fivefoldRepetitionB [p] = true
          · simp [certificateForcedMate, hcheck, hstable, hfive] at h
          · by_cases hclock : 150 ≤ p.halfmove
            · simp [certificateForcedMate, hcheck, hstable, hfive, hclock] at h
            · by_cases hturn : p.turn = c
              · have hex : ∃ m, m ∈ legalMoves p ∧
                    certificateForcedMate c (applyMove p m) n := by
                  simpa [certificateForcedMate, hcheck, hstable, hfive,
                    hclock, hturn] using h
                obtain ⟨m, hm, hchild⟩ := hex
                obtain ⟨child, hchild'⟩ := ih (applyMove p m) hchild
                have hlegal : legalMoveB p m = true :=
                  (legalMove_iff_legalMoveB p m).1 ((legalMoves_correct p m).1 hm)
                have hclock' : decide (p.halfmove < 150) = true := by
                  have hlt : p.halfmove < 150 := Nat.lt_of_not_ge hclock
                  simpa using hlt
                refine ⟨.mateAttacker m child, ?_⟩
                simp [checkMateCertificateB, hturn, hstable, hfive, hclock',
                  hlegal, hchild']
              · have hall : ∀ m, m ∈ legalMoves p →
                    certificateForcedMate c (applyMove p m) n := by
                  simpa [certificateForcedMate, hcheck, hstable, hfive,
                    hclock, hturn] using h
                let certFor : Move → MateCertificate := fun m =>
                  if hm : m ∈ legalMoves p then
                    Classical.choose (ih (applyMove p m) (hall m hm))
                  else .mateTerminal
                let xs : List (Move × MateCertificate) :=
                  (legalMoves p).map (fun m => (m, certFor m))
                have hcertFor (m : Move) (hm : m ∈ legalMoves p) :
                    checkMateCertificateB c (applyMove p m) n (certFor m) = true := by
                  dsimp [certFor]
                  rw [dif_pos hm]
                  exact Classical.choose_spec (ih (applyMove p m) (hall m hm))
                have hcover : (legalMoves p).all (fun m =>
                    xs.any (fun x => x.1 == m)) = true := by
                  apply List.all_eq_true.mpr
                  intro m hm
                  simp [xs, hm]
                have hchildren : xs.all (fun x =>
                    legalMoveB p x.1 &&
                      checkMateCertificateB c (applyMove p x.1) n x.2) = true := by
                  simp only [xs, List.all_map]
                  apply List.all_eq_true.mpr
                  intro m hm
                  simpa only [Function.comp_apply, Bool.and_eq_true] using
                    (show legalMoveB p m = true ∧
                        checkMateCertificateB c (applyMove p m) n (certFor m) = true from
                      ⟨(legalMove_iff_legalMoveB p m).1
                          ((legalMoves_correct p m).1 hm), hcertFor m hm⟩)
                have hclock' : decide (p.halfmove < 150) = true := by
                  have hlt : p.halfmove < 150 := Nat.lt_of_not_ge hclock
                  simpa using hlt
                have hreplies : certificateRepliesB p xs = true := by
                  simpa [certificateRepliesB] using hcover
                refine ⟨.mateDefender xs, ?_⟩
                simp [checkMateCertificateB, hturn, hstable, hfive, hclock',
                  hreplies, hchildren]

theorem mateCertificate_adequate (c : Color) (p : Position) (n : Nat) :
    (∃ cert, checkMateCertificateB c p n cert = true) ↔
      certificateForcedMate c p n := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact mateCertificate_sound c p n cert hcert
  · exact mateCertificate_complete c p n

/-!
# Rule-level certificate adequacy

The history-aware checker above fixes the automatic-draw policy.  This core
checker instead takes the terminal-position policy as an explicit Boolean
argument.  Its adequacy theorem therefore covers the finite rule kernel for
any such policy, including the no-draw rule layer used by the standalone
registry Challenge.
-/

def ruleCertificateRepliesB (p : Position)
    (xs : List (Move × MateCertificate)) : Bool :=
  certificateRepliesB p xs && xs.all (fun x => legalMoveB p x.1)

def ruleCertificateCheckB (terminal : Position → Bool)
    (c : Color) (p : Position) : Nat → MateCertificate → Bool
  | _, .mateTerminal => checkmateB p && (p.turn == Color.opposite c)
  | 0, .mateAttacker _ _ => false
  | 0, .mateDefender _ => false
  | n + 1, .mateAttacker m child =>
      (p.turn == c) && (!stalemateB p) && (!terminal p) && legalMoveB p m &&
        ruleCertificateCheckB terminal c (applyMove p m) n child
  | n + 1, .mateDefender xs =>
      (p.turn != c) && (!stalemateB p) && (!terminal p) &&
        ruleCertificateRepliesB p xs &&
        xs.all (fun x => legalMoveB p x.1 &&
          ruleCertificateCheckB terminal c (applyMove p x.1) n x.2)

noncomputable def ruleForcedMate (terminal : Position → Bool)
    (c : Color) (p : Position) : Nat → Prop
  | 0 => checkmateB p = true ∧ p.turn = Color.opposite c
  | n + 1 => by
      classical
      exact if checkmateB p = true then p.turn = Color.opposite c
      else if stalemateB p = true then False
      else if terminal p = true then False
      else if p.turn = c then
        ∃ m, m ∈ legalMoves p ∧
          ruleForcedMate terminal c (applyMove p m) n
      else
        ∀ m, m ∈ legalMoves p →
          ruleForcedMate terminal c (applyMove p m) n

theorem ruleCertificate_replies_iff (p : Position)
    (xs : List (Move × MateCertificate)) :
    ruleCertificateRepliesB p xs = true ↔
      (∀ m, m ∈ legalMoves p → ∃ x ∈ xs, x.1 = m) ∧
        (∀ x ∈ xs, legalMove p x.1) := by
  simp [ruleCertificateRepliesB, certificateRepliesB, legalMove_iff_legalMoveB]

theorem mateCertificate_rules_sound (terminal : Position → Bool)
    (c : Color) (p : Position) (n : Nat) (cert : MateCertificate)
    (h : ruleCertificateCheckB terminal c p n cert = true) :
    ruleForcedMate terminal c p n := by
  induction n generalizing p cert with
  | zero =>
      cases cert with
      | mateTerminal =>
          simpa [ruleCertificateCheckB, checkmateB, ruleForcedMate,
            Bool.and_eq_true] using h
      | mateAttacker m child =>
          simp [ruleCertificateCheckB] at h
      | mateDefender xs =>
          simp [ruleCertificateCheckB] at h
  | succ n ih =>
      cases cert with
      | mateTerminal =>
          have hh : checkmateB p = true ∧
              p.turn = Color.opposite c := by
            simpa [ruleCertificateCheckB, Bool.and_eq_true] using h
          simp [ruleForcedMate, hh.1, hh.2]
      | mateAttacker m child =>
          have h' : p.turn = c ∧ stalemateB p = false ∧
              terminal p = false ∧ legalMoveB p m = true ∧
              ruleCertificateCheckB terminal c (applyMove p m) n child = true := by
            simpa only [ruleCertificateCheckB, Bool.and_eq_true, beq_iff_eq,
              Bool.not_eq_true_eq_eq_false, and_assoc] using h
          rcases h' with ⟨hturn, hstable, hterminal, hlegal, hchild⟩
          have hlegal' : legalMove p m :=
            (legalMove_iff_legalMoveB p m).2 hlegal
          have hmem : m ∈ legalMoves p :=
            (legalMoves_correct p m).2 hlegal'
          have hcheck : checkmateB p = false := by
            by_contra hnot
            have : checkmateB p = true := Bool.eq_true_of_not_eq_false hnot
            have hparts : inCheckB p p.turn = true ∧
                (legalMoves p).isEmpty = true := by
              simpa [checkmateB] using this
            have hempty : legalMoves p = [] := by simpa using hparts.2
            simp [hempty] at hmem
          have hforced : ruleForcedMate terminal c (applyMove p m) n :=
            ih (applyMove p m) child hchild
          simp [ruleForcedMate, hcheck, hstable, hterminal, hturn]
          exact ⟨m, hmem, hforced⟩
      | mateDefender xs =>
          have h' : p.turn ≠ c ∧ stalemateB p = false ∧
              terminal p = false ∧ ruleCertificateRepliesB p xs = true ∧
              xs.all (fun x => legalMoveB p x.1 &&
                ruleCertificateCheckB terminal c (applyMove p x.1) n x.2) = true := by
            simpa only [ruleCertificateCheckB, Bool.and_eq_true, beq_iff_eq,
              bne_iff_ne, Bool.not_eq_true_eq_eq_false, and_assoc] using h
          rcases h' with ⟨hturn, hstable, hterminal, hreplies, hchildren⟩
          have hreplies' :
              (∀ m, m ∈ legalMoves p → ∃ x ∈ xs, x.1 = m) ∧
                (∀ x ∈ xs, legalMove p x.1) :=
            (ruleCertificate_replies_iff p xs).1 hreplies
          by_cases hcheck : checkmateB p = true
          · have hmate : p.turn = Color.opposite c := by
              have hturn' : p.turn ≠ c := hturn
              cases c <;> cases ht : p.turn <;> simp_all [Color.opposite]
            simp [ruleForcedMate, hcheck, hmate]
          · simp [ruleForcedMate, hcheck, hstable, hterminal, hturn]
            intro m hm
            obtain ⟨x, hx, hxm⟩ := hreplies'.1 m hm
            have hchild : ruleCertificateCheckB terminal c
                (applyMove p x.1) n x.2 = true := by
              have hall := (List.all_eq_true.mp hchildren) x hx
              have hall' : legalMoveB p x.1 = true ∧
                  ruleCertificateCheckB terminal c (applyMove p x.1) n x.2 = true := by
                simpa only [Bool.and_eq_true] using hall
              exact hall'.2
            simpa [hxm] using ih (applyMove p x.1) x.2 hchild

theorem mateCertificate_rules_complete (terminal : Position → Bool)
    (c : Color) (p : Position) (n : Nat)
    (h : ruleForcedMate terminal c p n) :
    ∃ cert, ruleCertificateCheckB terminal c p n cert = true := by
  induction n generalizing p with
  | zero =>
      refine ⟨.mateTerminal, ?_⟩
      simpa [ruleCertificateCheckB, ruleForcedMate, Bool.and_eq_true] using h
  | succ n ih =>
      by_cases hcheck : checkmateB p = true
      · have hturn : p.turn = Color.opposite c := by
          simpa [ruleForcedMate, hcheck] using h
        refine ⟨.mateTerminal, ?_⟩
        simpa [ruleCertificateCheckB, hturn] using hcheck
      · by_cases hstable : stalemateB p = true
        · simp [ruleForcedMate, hcheck, hstable] at h
        · by_cases hterminal : terminal p = true
          · simp [ruleForcedMate, hcheck, hstable, hterminal] at h
          · by_cases hturn : p.turn = c
            · have hex : ∃ m, m ∈ legalMoves p ∧
                    ruleForcedMate terminal c (applyMove p m) n := by
                  simpa [ruleForcedMate, hcheck, hstable, hterminal,
                    hturn] using h
              obtain ⟨m, hm, hchild⟩ := hex
              obtain ⟨child, hchild'⟩ := ih (applyMove p m) hchild
              have hlegal : legalMoveB p m = true :=
                (legalMove_iff_legalMoveB p m).1 ((legalMoves_correct p m).1 hm)
              refine ⟨.mateAttacker m child, ?_⟩
              simp [ruleCertificateCheckB, hturn, hstable, hterminal,
                hlegal, hchild']
            · have hall : ∀ m, m ∈ legalMoves p →
                    ruleForcedMate terminal c (applyMove p m) n := by
                  simpa [ruleForcedMate, hcheck, hstable, hterminal,
                    hturn] using h
              let certFor : Move → MateCertificate := fun m =>
                if hm : m ∈ legalMoves p then
                  Classical.choose (ih (applyMove p m) (hall m hm))
                else .mateTerminal
              let xs : List (Move × MateCertificate) :=
                (legalMoves p).map (fun m => (m, certFor m))
              have hcertFor (m : Move) (hm : m ∈ legalMoves p) :
                    ruleCertificateCheckB terminal c (applyMove p m) n
                      (certFor m) = true := by
                dsimp [certFor]
                rw [dif_pos hm]
                exact Classical.choose_spec (ih (applyMove p m) (hall m hm))
              have hcover : (legalMoves p).all (fun m =>
                    xs.any (fun x => x.1 == m)) = true := by
                apply List.all_eq_true.mpr
                intro m hm
                simp [xs, hm]
              have hchildren : xs.all (fun x =>
                    legalMoveB p x.1 &&
                      ruleCertificateCheckB terminal c (applyMove p x.1) n x.2) = true := by
                simp only [xs, List.all_map]
                apply List.all_eq_true.mpr
                intro m hm
                simpa only [Function.comp_apply, Bool.and_eq_true] using
                  (show legalMoveB p m = true ∧
                      ruleCertificateCheckB terminal c (applyMove p m) n
                        (certFor m) = true from
                    ⟨(legalMove_iff_legalMoveB p m).1
                        ((legalMoves_correct p m).1 hm), hcertFor m hm⟩)
              have hlegalall : xs.all (fun x => legalMoveB p x.1) = true := by
                simp only [xs, List.all_map]
                apply List.all_eq_true.mpr
                intro m hm
                exact (legalMove_iff_legalMoveB p m).1
                  ((legalMoves_correct p m).1 hm)
              have hreplies : ruleCertificateRepliesB p xs = true := by
                have hcoverage : certificateRepliesB p xs = true := by
                  simpa [certificateRepliesB] using hcover
                simp [ruleCertificateRepliesB, hcoverage, hlegalall]
              refine ⟨.mateDefender xs, ?_⟩
              simp [ruleCertificateCheckB, hturn, hstable, hterminal,
                hreplies, hchildren]

theorem mateCertificate_rules_adequate (terminal : Position → Bool)
    (c : Color) (p : Position) (n : Nat) :
    (∃ cert, ruleCertificateCheckB terminal c p n cert = true) ↔
      ruleForcedMate terminal c p n := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact mateCertificate_rules_sound terminal c p n cert hcert
  · exact mateCertificate_rules_complete terminal c p n

end Chess
