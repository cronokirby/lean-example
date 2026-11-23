module

public import Examples.Nsl.Lawful
public import Examples.Nsl.Secrecy.Model

/-! # The symbolic world refines the abstract step `PStep`

Specs of the `Env` operations of `Symbolic` and of `nsl.step` in the symbolic
world with Lowe's check: every step returns, and its effect on the leaked flag,
the table and the sessions is a `PStep`. Counters and vector lengths grow by
at most one per step, which is how the overflow checks are discharged.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Secrecy

theorem ok_of_spec {α : Type _} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ x, m = ok x ∧ p x := by
  cases m <;> simp_all

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

/-- The counters of the symbolic world, and how they may grow in one step. -/
structure Frame (env env' : Symbolic P T U Seed Coins Pk Sk Ct) : Prop where
  secret : env'.secret = env.secret
  tape : env'.tape = env.tape
  oracle_tape : env'.oracle.tape = env.oracle.tape
  count : env'.count.val ≤ env.count.val + 1
  oracle_count : env'.oracle.count.val ≤ env.oracle.count.val + 1
  table : env'.table.length ≤ env.table.length + 1
  guesses : env'.guesses.length ≤ env.guesses.length + 1

theorem Frame.refl (env : Symbolic P T U Seed Coins Pk Sk Ct) : Frame env env :=
  ⟨rfl, rfl, rfl, by omega, by omega, by omega, by omega⟩

@[step] theorem sym_nonce.spec (hT : TI.Total) (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (i : Std.Usize) :
    Symbolic.Insts.ExamplesNslEnvClause0_CtSym.nonce E TI UI env i ⦃ n env' =>
      env' = env ∧ ∃ x, n = if i = env.secret then .Secret else .Val x ⦄ := by
  unfold Symbolic.Insts.ExamplesNslEnvClause0_CtSym.nonce
  split
  · simp_all
  · obtain ⟨x, hx⟩ := hT.nonce_ok env.tape i
    simp_all

@[step] theorem sym_same.spec (env : Symbolic P T U Seed Coins Pk Sk Ct) (a b : Sym)
    (hg : env.guesses.length < Usize.max) :
    Symbolic.Insts.ExamplesNslEnvClause0_CtSym.same E TI UI env a b ⦃ r env' =>
      (r = true → a = b) ∧ env'.tape = env.tape ∧ env'.oracle = env.oracle ∧
      env'.secret = env.secret ∧ env'.table = env.table ∧ env'.count = env.count ∧
      env'.leaked = env.leaked ∧ env'.guesses.length ≤ env.guesses.length + 1 ⦄ := by
  unfold Symbolic.Insts.ExamplesNslEnvClause0_CtSym.same
  cases a <;> cases b <;> step* <;> simp_all

end examples.nsl.Secrecy


namespace examples.nsl.Secrecy

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

include E in
@[step] theorem ct_eq.spec (hE : E.Total) (a b : Ct) :
    E.corecmpEqInst.partialEqInst.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  simp [hE.eq_ok]

@[step] theorem lookup_loop.spec {N : Type _} (hE : E.Total) (table : Slice (Entry Ct N))
    (who : Std.U8) (c : Ct) (i : Std.Usize) :
    lookup_loop E.coremarkerCopyInst E.corecmpEqInst table who c i ⦃ o =>
      ∀ m, o = some m → ∃ e ∈ table.val, e.to = who ∧ e.msg = m ⦄ := by
  unfold lookup_loop
  step*
  · intro m hm
    cases hm
    refine ⟨e, ?_, ?_, ?_⟩ <;> simp_all
termination_by table.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step] theorem real_dec.spec (hE : E.Total) (hU : UI.Total) (o : RealOracle P U) (who : Std.U8)
    (c : Ct) :
    RealOracle.Insts.ExamplesNslOracle.dec E UI o who c ⦃ _ o' => o' = o ⦄ := by
  unfold RealOracle.Insts.ExamplesNslOracle.dec
  obtain ⟨s, hs⟩ := hU.seed_ok o.tape who
  obtain ⟨⟨pk, sk⟩, hk⟩ := hE.keygen_ok s
  obtain ⟨m, hm⟩ := hE.dec_ok sk c
  simp [hs, hk, hm]

@[step] theorem real_enc.spec (hE : E.Total) (hU : UI.Total) (o : RealOracle P U) (dst : Std.U8)
    (m : Msg Std.U64) (h : o.count.val < Usize.max) :
    RealOracle.Insts.ExamplesNslOracle.enc E UI o dst m ⦃ _ o' =>
      o'.tape = o.tape ∧ o'.count.val = o.count.val + 1 ⦄ := by
  unfold RealOracle.Insts.ExamplesNslOracle.enc RealOracle.Insts.ExamplesNslOracle.pk
  obtain ⟨s, hs⟩ := hU.seed_ok o.tape dst
  obtain ⟨⟨pk, sk⟩, hk⟩ := hE.keygen_ok s
  obtain ⟨r, hr⟩ := hU.coins_ok o.tape o.count
  obtain ⟨c, hc⟩ := hE.enc_ok pk m r
  simp only [hs, hk, hr, bind_ok]
  have hc' : E.enc pk m r ⦃ x => x = c ⦄ := by rw [hc]; simp
  step with hc'
  step*

@[step] theorem symbolize.spec (m : Msg Std.U64) : symbolize m ⦃ m' => msgClean m' ⦄ := by
  unfold symbolize; split <;> simp [msgClean]

@[step] theorem concretize.spec (m : Msg Sym) :
    concretize m ⦃ o => (o = none ↔ ¬ msgClean m) ⦄ := by
  unfold concretize; split <;> split <;> (try split) <;> simp_all [msgClean]

@[step] theorem sym_dec.spec (hE : E.Total) (hU : UI.Total) (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (who : Std.U8) (c : Ct) :
    Symbolic.Insts.ExamplesNslEnvClause0_CtSym.dec E TI UI env who c ⦃ o env' =>
      env' = env ∧ ∀ m, o = some m → decOk env.table.val who m ⦄ := by
  unfold Symbolic.Insts.ExamplesNslEnvClause0_CtSym.dec
  step*
  all_goals simp_all [decOk, alloc.vec.Vec.deref, alloc.vec.Vec.val]

end examples.nsl.Secrecy


namespace examples.nsl.Secrecy

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

@[step] theorem pke_keygen.spec (hE : E.Total) (s : Seed) : E.keygen s ⦃ _ => True ⦄ := by
  obtain ⟨k, hk⟩ := hE.keygen_ok s; simp [hk]

@[step] theorem pke_enc.spec (hE : E.Total) (pk : Pk) (m : Msg Std.U64) (r : Coins) :
    E.enc pk m r ⦃ _ => True ⦄ := by
  obtain ⟨k, hk⟩ := hE.enc_ok pk m r; simp [hk]

@[step] theorem tape_seed.spec {X : Type _} {XI : Tape X Seed Coins} (hX : XI.Total) (t : X)
    (a : Std.U8) : XI.seed t a ⦃ _ => True ⦄ := by
  obtain ⟨k, hk⟩ := hX.seed_ok t a; simp [hk]

@[step] theorem tape_coins.spec {X : Type _} {XI : Tape X Seed Coins} (hX : XI.Total) (t : X)
    (i : Std.Usize) : XI.coins t i ⦃ _ => True ⦄ := by
  obtain ⟨k, hk⟩ := hX.coins_ok t i; simp [hk]

@[step] theorem sym_enc.spec (hE : E.Total) (hT : TI.Total) (hU : UI.Total)
    (env : Symbolic P T U Seed Coins Pk Sk Ct) (dst : Std.U8) (m : Msg Sym)
    (h1 : env.count.val < Usize.max) (h2 : env.oracle.count.val < Usize.max)
    (h3 : env.table.length < Usize.max) :
    Symbolic.Insts.ExamplesNslEnvClause0_CtSym.enc E TI UI env dst m ⦃ ct env' =>
      env'.tape = env.tape ∧ env'.oracle.tape = env.oracle.tape ∧ env'.secret = env.secret ∧
      env'.guesses = env.guesses ∧ env'.count.val ≤ env.count.val + 1 ∧
      env'.oracle.count.val ≤ env.oracle.count.val + 1 ∧
      env'.table.length ≤ env.table.length + 1 ∧
      sent dst m ct env.leaked env.table.val env'.leaked env'.table.val ⦄ := by
  unfold Symbolic.Insts.ExamplesNslEnvClause0_CtSym.enc
  split
  · step*
    rcases o with _ | m2 <;> step* <;> and_intros <;> simp_all
  · step*
    and_intros <;> simp_all

end examples.nsl.Secrecy


namespace examples.nsl.Secrecy

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

theorem PStep.skip' {σ : Nat} {l l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss : List (Session Sym)} (h1 : l' = l) (h2 : tab' = tab) : PStep σ l tab ss l' tab' ss := by
  subst h1 h2; exact .skip

theorem fresh_eq (ss : alloc.vec.Vec (Session Sym)) (sec : Std.Usize) (x : Std.U64) :
    (if ss.len = sec then Sym.Secret else Sym.Val x) = fresh sec.val ss.val x := by
  unfold fresh
  split <;> split <;> first | rfl | (exfalso; scalar_tac)

/-- **Spec of `nsl.step` in the symbolic world with Lowe's check.** -/
@[step] theorem sym_step.spec (hE : E.Total) (hT : TI.Total) (hU : UI.Total)
    (env : Symbolic P T U Seed Coins Pk Sk Ct) (ss : alloc.vec.Vec (Session Sym)) (a : Action Ct)
    (h1 : env.count.val < Usize.max) (h2 : env.oracle.count.val < Usize.max)
    (h3 : env.table.length < Usize.max) (h4 : env.guesses.length < Usize.max)
    (h5 : ss.length < Usize.max) :
    step (Symbolic.Insts.ExamplesNslEnvClause0_CtSym E TI UI) true env ss a ⦃ _ env' ss' =>
      PStep env.secret.val env.leaked env.table.val ss.val env'.leaked env'.table.val ss'.val ∧
      Frame env env' ∧ ss'.length ≤ ss.length + 1 ⦄ := by
  unfold step
  cases a with
  | Start owner peer =>
    step*
    · exact ⟨.skip, Frame.refl _, by omega⟩
    · subst env1_post
      rw [fresh_eq] at na_post; subst na_post
      refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [sessions1_post]; exact .start owner peer x t ‹_› t_post7
      all_goals simp_all
  | Respond owner msg =>
    step*
    · exact ⟨.skip, Frame.refl _, by omega⟩
    · subst env1_post; exact ⟨.skip, Frame.refl _, by omega⟩
    · subst env1_post env2_post
      rw [fresh_eq] at nb_post; subst nb_post
      refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [sessions1_post]
        exact .respond owner peer na x t ‹_› (o_post _ (by simp_all)) t_post7
      all_goals simp_all
    · subst env1_post; exact ⟨.skip, Frame.refl _, by omega⟩
    · subst env1_post; exact ⟨.skip, Frame.refl _, by omega⟩
  | Deliver session msg =>
    step*
    -- Every rejection leaves the state unchanged except for the guesses.
    all_goals try first
      | exact ⟨.skip, Frame.refl _, by omega⟩
      | (subst_vars; exact ⟨.skip, Frame.refl _, by omega⟩)
      | (refine ⟨PStep.skip' ?_ ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩ <;> simp_all)
    · -- An initiator accepts message two.
      subst env1 index_mut_back
      have hj : ss.val[session.val]? = some (.Initiating owner peer na) := by
        rw [List.getElem?_eq_getElem (by scalar_tac)]; simp_all
      have hdec : decOk env.table.val owner (.Two na nb peer) := by
        have h := o_post m ‹_›
        have hb : na2 = na := b_post ‹_›
        have hr : responder = peer :=
          UScalar.eq_of_val_eq (by simpa using ‹¬(responder != peer) = true›)
        rw [‹m = _›, hb, hr] at h; exact h
      have he : env2.leaked = env.leaked ∧ env2.table = env.table := by simp_all
      rw [he.1, he.2] at t_post7
      refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [alloc.vec.Vec.set_val_eq]
        exact .deliverI session.val owner peer na nb t hj hdec t_post7
      all_goals simp_all
    · -- A responder accepts message three.
      subst env1 index_mut_back
      have hj : ss.val[session.val]? = some (.Responding owner peer na nb) := by
        rw [List.getElem?_eq_getElem (by scalar_tac)]; simp_all
      have hdec : decOk env.table.val owner (.Three nb) := by
        have h := o_post m ‹_›
        have hb : nb2 = nb := b_post ‹_›
        rw [‹m = _›, hb] at h; exact h
      have he : env2.leaked = env.leaked ∧ env2.table = env.table := by simp_all
      refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [alloc.vec.Vec.set_val_eq, he.1, he.2]
        exact .deliverR session.val owner peer na nb hj hdec
      all_goals simp_all

end examples.nsl.Secrecy

