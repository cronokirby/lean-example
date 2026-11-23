module

public import Examples.Nsl.Lawful
public import Examples.Nsl.Faithful.Spec

/-! # One step of the ideal and symbolic worlds side by side

`Related` says that an ideal world (`World` over `IdealOracle`) and its
sessions are a symbolic world (`Symbolic`) and its sessions with the symbol
`Sym.Secret` replaced by a number `n`: the tapes agree except that the ideal
one has nonce `n` for the secret session, the oracle tapes and counters are
equal, and the tables and sessions agree entrywise after the substitution.

`faithful_step`: every action, run in both worlds, keeps them related as long
as the symbolic run did not record `n` as a guess, and gives the adversary the
same response as long as the symbolic run did not leak.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl

/-- `omega` after unfolding `Vec.length`. -/
macro "vomega" : tactic => `(tactic| ((try simp only [alloc.vec.Vec.length] at *) <;> omega))

open Model Spec

variable {P T1 T2 U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI1 : Tape T1 Seed Coins} {TI2 : Tape T2 Seed Coins} {UI : Tape U Seed Coins}

/-- The ideal world `e1` with sessions `s1` is the symbolic world `e2` with
sessions `s2` and secret session `j`, where the secret is the nonce `n`. -/
def Related (TI1 : Tape T1 Seed Coins) (TI2 : Tape T2 Seed Coins) (j : Std.Usize) (n : Std.U64)
    (e1 : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct)) (s1 : alloc.vec.Vec (Session Std.U64))
    (e2 : Symbolic P T2 U Seed Coins Pk Sk Ct) (s2 : alloc.vec.Vec (Session Sym)) : Prop :=
  (∀ a, TI1.seed e1.tape a = TI2.seed e2.tape a) ∧
  (∀ i, TI1.coins e1.tape i = TI2.coins e2.tape i) ∧
  (∀ k, k ≠ j → TI1.nonce e1.tape k = TI2.nonce e2.tape k) ∧
  TI1.nonce e1.tape j = ok n ∧
  e1.oracle.real.tape = e2.oracle.tape ∧ e2.secret = j ∧
  e1.count = e2.count ∧ e1.oracle.real.count = e2.oracle.count ∧
  e1.oracle.table.val = e2.table.val.map (entryMap (subst n)) ∧
  s1.val = s2.val.map (sessMap (subst n))

/-- After `k` steps the symbolic world's counters and vectors have at most `k`
entries. -/
def SymBnd (k : Nat) (e : Symbolic P T2 U Seed Coins Pk Sk Ct) (s : alloc.vec.Vec (Session Sym)) :
    Prop :=
  e.count.val ≤ k ∧ e.oracle.count.val ≤ k ∧ e.table.length ≤ k ∧ e.guesses.length ≤ k ∧
    s.length ≤ k

/-- After `k` steps the ideal world's counters and vectors have at most `k`
entries. -/
def IdealBnd (k : Nat) (e : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct))
    (s : alloc.vec.Vec (Session Std.U64)) : Prop :=
  e.count.val ≤ k ∧ e.oracle.real.count.val ≤ k ∧ e.oracle.table.length ≤ k ∧ s.length ≤ k

theorem tapeRel_of_related (hT1 : TI1.Total) (hT2 : TI2.Total) {j : Std.Usize} {n : Std.U64}
    {e1 : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct)} {s1 : alloc.vec.Vec (Session Std.U64)}
    {e2 : Symbolic P T2 U Seed Coins Pk Sk Ct} {s2 : alloc.vec.Vec (Session Sym)}
    (h : Related TI1 TI2 j n e1 s1 e2 s2) :
    TapeRel j n (tapeF hT1 e1.tape) (tapeF hT2 e2.tape) := by
  obtain ⟨hs, hc, hn, hj, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext a; have := hs a; rw [seed_eq hT1, seed_eq hT2] at this; simpa using this
  · funext i; have := hc (natU i); rw [coins_natU hT1, coins_natU hT2] at this; simpa using this
  · intro k hk; have := hn k hk; rw [nonce_eq hT1, nonce_eq hT2] at this; simpa using this
  · rw [nonce_eq hT1] at hj; simpa using hj

/-- **One step in the ideal world alone.** It does not fail, keeps the tapes,
creates at most one session, never changes a session's peer, and increments
each counter at most once. -/
theorem ideal_step_ok (hE : E.Total) (hT1 : TI1.Total) (hU : UI.Total) (lowe : Bool) (k : Nat)
    (hk : k < Usize.max) (e1 : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct))
    (s1 : alloc.vec.Vec (Session Std.U64)) (hb : IdealBnd k e1 s1) (a : Action Ct) :
    ∃ r e1' s1', step (idealInst E TI1 UI) lowe e1 s1 a = ok (r, e1', s1') ∧
      IdealBnd (k + 1) e1' s1' ∧ e1'.tape = e1.tape ∧ e1'.oracle.real.tape = e1.oracle.real.tape ∧
      ∀ i (h : i < s1.length), ∃ h' : i < s1'.length, peerF s1'.val[i] = peerF s1.val[i] := by
  obtain ⟨b1, b2, b3, b4⟩ := hb
  simp only [alloc.vec.Vec.length] at b3 b4
  obtain ⟨⟨r, e1', s1'⟩, heq, hp, hf1, hf2⟩ := exists_of_spec (ideal_step hE hT1 hU e1.tape
    e1.oracle.real.tape lowe e1 s1 a ⟨rfl, rfl⟩ ⟨by vomega, by vomega, by vomega⟩ (by vomega))
  have hi := idealStep_facts _ _ _ _ _ _ _ _ _ _ hp
  have hs := pstep_sessions _ _ _ _ _ _ _ _ hp
  simp only [absI] at hi
  refine ⟨r, e1', s1', heq, ⟨by vomega, by vomega, by simp only [alloc.vec.Vec.length]; omega,
    by simp only [alloc.vec.Vec.length]; omega⟩,
    hf1, hf2, fun i h => ?_⟩
  obtain ⟨h', hpe⟩ := hs.2.2 i h
  exact ⟨h', hpe⟩

/-- **One step in both worlds.** From related worlds, after at most `k <
Usize.max` steps, an action runs without failure in both. The symbolic run
records at most one guess (extending the list) and keeps `leaked` set. If `n`
is not among the symbolic run's guesses afterwards, the worlds are still
related, and if moreover nothing leaked, the responses are equal. -/
theorem faithful_step (hE : E.Total) (hT1 : TI1.Total) (hT2 : TI2.Total) (hU : UI.Total)
    (lowe : Bool) (j : Std.Usize) (n : Std.U64) (k : Nat) (hk : k < Usize.max)
    (e1 : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct)) (s1 : alloc.vec.Vec (Session Std.U64))
    (e2 : Symbolic P T2 U Seed Coins Pk Sk Ct) (s2 : alloc.vec.Vec (Session Sym))
    (hR : Related TI1 TI2 j n e1 s1 e2 s2) (hb : SymBnd k e2 s2) (a : Action Ct) :
    ∃ r1 e1' s1' r2 e2' s2',
      step (idealInst E TI1 UI) lowe e1 s1 a = ok (r1, e1', s1') ∧
      step (symInst E TI2 UI) lowe e2 s2 a = ok (r2, e2', s2') ∧
      SymBnd (k + 1) e2' s2' ∧ e2.guesses.val <+: e2'.guesses.val ∧
      (e2.leaked = true → e2'.leaked = true) ∧
      (n ∉ e2'.guesses.val →
        Related TI1 TI2 j n e1' s1' e2' s2' ∧ (e2'.leaked = false → r1 = r2)) := by
  have htr := tapeRel_of_related hT1 hT2 hR
  obtain ⟨hs, hc, hn, hj, hu, hsec, hcnt, hocnt, htab, hss⟩ := hR
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  simp only [alloc.vec.Vec.length] at b3 b4 b5
  have ht1 : e1.oracle.table.val.length = e2.table.val.length := by
    simp only [htab, List.length_map]
  have hs1 : s1.val.length = s2.val.length := by simp only [hss, List.length_map]
  obtain ⟨⟨r1, e1', s1'⟩, heq1, hp1, hf1, hf1'⟩ := exists_of_spec (ideal_step hE hT1 hU e1.tape
    e1.oracle.real.tape lowe e1 s1 a ⟨rfl, rfl⟩
    ⟨by rw [hcnt]; vomega, by rw [hocnt]; vomega, by vomega⟩ (by vomega))
  obtain ⟨⟨r2, e2', s2'⟩, heq2, hp2, hf2, hf2', hf2''⟩ := exists_of_spec (sym_step hE hT2 hU e2.tape
    e2.oracle.tape e2.secret lowe e2 s2 a ⟨rfl, rfl, rfl⟩ ⟨by vomega, by vomega, by vomega⟩
    (by simp only [roomSS]; vomega) (by vomega))
  have hfs := symStep_facts _ _ _ _ _ _ _ _ _ _ _ hp2
  have hss2 := pstep_sessions _ _ _ _ _ _ _ _ hp2
  simp only [absS] at hfs
  refine ⟨r1, e1', s1', r2, e2', s2', heq1, heq2, ?_, hfs.1, hfs.2.2.1, fun hng => ?_⟩
  · have hgl := hfs.2.1
    refine ⟨by vomega, by vomega, ?_, ?_, ?_⟩
    · simp only [alloc.vec.Vec.length]; omega
    · simp only [alloc.vec.Vec.length]; omega
    · simp only [alloc.vec.Vec.length]; omega
  · have hp1' : pstep (idealEnv (pkeF hE) (tapeF hT1 e1.tape) (tapeF hU e2.oracle.tape)) lowe
        (absI e1) (s2.val.map (sessMap (subst n))) a = (r1, absI e1', s1'.val) := by
      rw [← hss, ← hu]; exact hp1
    have hRA : RelA n (absI e1) (absS e2) := ⟨by simp [absI, absS, hcnt], by simp [absI, absS, hocnt],
      by simp [absI, absS, htab]⟩
    rw [hsec] at hp2
    obtain ⟨⟨c1, c2, c3⟩, hs', hr⟩ := rel_step (pkeF hE) _ _ _ j n htr lowe (absI e1) (absS e2)
      s2.val a hRA r1 (absI e1') s1'.val hp1' r2 (absS e2') s2'.val hp2 (by simpa [absS] using hng)
    simp only [absI, absS] at c1 c2 c3 hr
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c3, hs'⟩, hr⟩
    · rw [hf1, hf2]; exact hs
    · rw [hf1, hf2]; exact hc
    · rw [hf1, hf2]; exact hn
    · rw [hf1]; exact hj
    · rw [hf1', hf2', hu]
    · rw [hf2'', hsec]
    · exact UScalar.eq_of_val_eq c1
    · exact UScalar.eq_of_val_eq c2

/-- One ideal step, in the form ~run_loop_refines~ uses. -/
theorem ideal_hstep (hE : E.Total) (hT1 : TI1.Total) (hU : UI.Total) (t : T1) (u : U) (lowe : Bool)
    (k : Nat) (e : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct))
    (s : alloc.vec.Vec (Session Std.U64)) (a : Action Ct) (hk : k < Usize.max)
    (h : frameI t u e ∧ IdealBnd k e s) :
    ∃ r e' s', step (idealInst E TI1 UI) lowe e s a = ok (r, e', s') ∧
      pstep (idealPE hE hT1 hU t u) lowe (absI e) s.val a = (r, absI e', s'.val) ∧
      (frameI t u e' ∧ IdealBnd (k + 1) e' s') := by
  obtain ⟨hI, b1, b2, b3, b4⟩ := h
  obtain ⟨⟨r, e', s'⟩, heq, hp, hf⟩ := exists_of_spec (ideal_step hE hT1 hU t u lowe e s a hI
    ⟨by vomega, by vomega, by vomega⟩ (by vomega))
  have hi := idealStep_facts _ _ _ _ _ _ _ _ _ _ hp
  have hs := pstep_sessions _ _ _ _ _ _ _ _ hp
  simp only [absI] at hi
  exact ⟨r, e', s', heq, hp, hf, by vomega, by vomega, by vomega, by vomega⟩

/-- One symbolic step, in the form ~run_loop_refines~ uses. -/
theorem sym_hstep (hE : E.Total) (hT2 : TI2.Total) (hU : UI.Total) (t : T2) (u : U)
    (j : Std.Usize) (lowe : Bool)
    (k : Nat) (e : Symbolic P T2 U Seed Coins Pk Sk Ct)
    (s : alloc.vec.Vec (Session Sym)) (a : Action Ct) (hk : k < Usize.max)
    (h : frameS t u j e ∧ SymBnd k e s) :
    ∃ r e' s', step (symInst E TI2 UI) lowe e s a = ok (r, e', s') ∧
      pstep (symPE hE hT2 hU t u j) lowe (absS e) s.val a = (r, absS e', s'.val) ∧
      (frameS t u j e' ∧ SymBnd (k + 1) e' s') := by
  obtain ⟨hI, b1, b2, b3, b4, b5⟩ := h
  obtain ⟨⟨r, e', s'⟩, heq, hp, hf⟩ := exists_of_spec (sym_step hE hT2 hU t u j lowe e s a hI
    ⟨by vomega, by vomega, by vomega⟩ (by simp only [roomSS]; vomega) (by vomega))
  have hi := symStep_facts _ _ _ _ _ _ _ _ _ _ _ hp
  have hs := pstep_sessions _ _ _ _ _ _ _ _ hp
  simp only [absS] at hi
  exact ⟨r, e', s', heq, hp, hf, by vomega, by vomega, by vomega, by vomega, by vomega⟩

end examples.nsl
