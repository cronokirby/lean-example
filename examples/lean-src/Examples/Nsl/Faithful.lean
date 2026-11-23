module

public import Examples.Nsl.Lawful
public import Examples.Nsl.Faithful.Step
import Examples.Nsl.Faithful.Run

/-! # Faithfulness of the symbolic world

The ideal world (`World` over `IdealOracle`, with nonce `n` for session
`secret`) gives the adversary the same responses as the symbolic world, unless
the symbolic run leaked the secret or compared it with `n`.

* `faithful_step` (in `Examples.Nsl.Faithful.Step`) is the stepwise form: from
  related worlds, one action keeps them related while `n` is not a recorded
  guess, with equal responses while nothing leaked.
* `faithful_holds` is the list form: the Rust property `faithful` returns
  `true` for every `lowe`, every total `Pke` and total tapes, and all
  inputs.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model Spec

section

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}

public theorem Override.total (hT : TI.Total) : (Override.Insts.ExamplesNslTape TI).Total where
  seed_ok t a := by simpa [Override.Insts.ExamplesNslTape.seed] using hT.seed_ok t.inner a
  coins_ok t i := by simpa [Override.Insts.ExamplesNslTape.coins] using hT.coins_ok t.inner i
  nonce_ok t k := by
    simp only [Override.Insts.ExamplesNslTape, Override.Insts.ExamplesNslTape.nonce]
    split
    · exact ⟨_, rfl⟩
    · exact hT.nonce_ok t.inner k

theorem contains_loop_spec (values : Slice Std.U64) (n : Std.U64) (i : Std.Usize)
    (hi : i.val ≤ values.length) :
    contains_loop values n i ⦃ b => b = decide (n ∈ values.val.drop i.val) ⦄ := by
  unfold contains_loop
  dsimp only
  split
  · step
    split
    · simp only [WP.spec_ok]
      subst_vars
      rw [List.drop_eq_getElem_cons (by scalar_tac : i.val < values.val.length)]
      simp only [List.mem_cons, true_or, decide_true, eq_self_iff_true]
    · step*
      rw [List.drop_eq_getElem_cons (by scalar_tac : i.val < values.val.length)]
      simp_all [eq_comm]
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by values.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem same_response_self (hE : E.Total) (r : Response Ct) :
    same_response E.coremarkerCopyInst E.corecmpEqInst r r = ok true := by
  cases r <;> simp [same_response, hE.eq_ok]

theorem faithful_loop_true (hE : E.Total)
    (ideal : World P (Override T) (IdealOracle P U Seed Coins Pk Sk Ct))
    (seen sym_seen : alloc.vec.Vec (Response Ct)) (i : Std.Usize) (h : seen.val = sym_seen.val) :
    faithful_loop E TI ideal seen sym_seen i ⦃ b => b = true ⦄ := by
  unfold faithful_loop
  have hl : seen.length = sym_seen.length := by simp [alloc.vec.Vec.length, h]
  step*
  have : r = r1 := by simp [r_post, r1_post, h]
  subst this
  rw [same_response_self hE]; simp only [bind_ok, ite_true]
  step*
termination_by seen.length - i.val
decreasing_by scalar_decr_tac

/-- **Faithfulness of the symbolic world.** For both protocols (every `lowe`),
every total `Pke`, total tapes, tape, oracle tape, list of actions, secret
session index and nonce `n`, the Rust property `faithful` returns `true` (and
does not panic): running the actions in the ideal world with nonce `n` for
session `secret` gives the same responses as the symbolic world, unless the
symbolic run leaked the secret or compared it with `n`. -/
public theorem faithful_holds (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (lowe : Bool)
    (tape : T) (oracle_tape : U) (actions : Slice (Action Ct)) (secret : Std.Usize)
    (n : Std.U64) :
    faithful E TI UI lowe tape oracle_tape actions secret n = ok true := by
  have hO := Override.total hT
  let fixed : Override T := { inner := tape, session := secret, nonce := n }
  let ro : RealOracle P U := { tape := oracle_tape, count := 0#usize, pke := () }
  let io : IdealOracle P U Seed Coins Pk Sk Ct := { real := ro, table := alloc.vec.Vec.new _ }
  let e1 : World P (Override T) (IdealOracle P U Seed Coins Pk Sk Ct) :=
    { tape := fixed, oracle := io, count := 0#usize, pke := () }
  let e2 : Symbolic P (Override T) U Seed Coins Pk Sk Ct :=
    { tape := fixed, oracle := ro, secret := secret, table := alloc.vec.Vec.new _,
      count := 0#usize, guesses := alloc.vec.Vec.new _, leaked := false }
  obtain ⟨⟨e1', s1', seen1⟩, heq1, ha1, -, hseen1, -⟩ := exists_of_spec
    (run_loop_refines (lowe := lowe) (idealInst E (Override.Insts.ExamplesNslTape TI) UI)
      (idealPE hE hO hU fixed oracle_tape) absI
      (fun k e s => frameI fixed oracle_tape e ∧ IdealBnd k e s)
      (fun k e s a hk h => ideal_hstep hE hO hU fixed oracle_tape lowe k e s a hk h)
      actions e1 (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) 0#usize (by simp)
      ⟨⟨rfl, rfl⟩, by simp [IdealBnd, e1, io, ro]⟩ (by simp))
  obtain ⟨⟨e2', s2', seen2⟩, heq2, ha2, -, hseen2, -⟩ := exists_of_spec
    (run_loop_refines (lowe := lowe) (symInst E (Override.Insts.ExamplesNslTape TI) UI)
      (symPE hE hO hU fixed oracle_tape secret) absS
      (fun k e s => frameS fixed oracle_tape secret e ∧ SymBnd k e s)
      (fun k e s a hk h => sym_hstep hE hO hU fixed oracle_tape secret lowe k e s a hk h)
      actions e2 (alloc.vec.Vec.new _) (alloc.vec.Vec.new _) 0#usize (by simp)
      ⟨⟨rfl, rfl, rfl⟩, by simp [SymBnd, e2, ro]⟩ (by simp))
  have hr1 : run E.coremarkerCopyInst (idealInst E (Override.Insts.ExamplesNslTape TI) UI) lowe e1
      actions = ok ((s1', seen1), e1') := by
    unfold run; rw [heq1]; simp
  have hr2 : run E.coremarkerCopyInst (symInst E (Override.Insts.ExamplesNslTape TI) UI) lowe e2
      actions = ok ((s2', seen2), e2') := by
    unfold run; rw [heq2]; simp
  unfold faithful
  simp only [IdealOracle.new, RealOracle.new, World.new, Symbolic.new, bind_ok]
  rw [hr1]
  simp only [bind_ok]
  rw [hr2]
  simp only [bind_ok]
  show (if e2'.leaked = true then ok true else do
      let b ← contains e2'.guesses.deref n
      if b = true then ok true else faithful_loop E TI e1' seen1 seen2 0#usize) = ok true
  split
  · rfl
  rename_i hl
  have hc := eq_ok_of_spec (contains_loop_spec (alloc.vec.Vec.deref e2'.guesses) n 0#usize (by simp))
  simp only [contains] at *
  rw [hc]
  simp only [bind_ok]
  split
  · rfl
  rename_i hn
  apply eq_ok_of_spec
  apply faithful_loop_true hE
  -- The responses agree, by `prun_faithful`.
  have htr : TapeRel secret n (tapeF hO fixed) (tapeF hO fixed) := by
    refine ⟨rfl, rfl, fun _ _ => rfl, ?_⟩
    have := nonce_eq hO fixed secret
    simp [Override.Insts.ExamplesNslTape, Override.Insts.ExamplesNslTape.nonce, fixed] at this
    exact this.symm
  have hRA : RelA n (absI e1) (absS e2) := by simp [RelA, absI, absS, e1, e2, io, ro]
  have hpf := prun_faithful (pkeF hE) (tapeF hO fixed) (tapeF hO fixed) (tapeF hU oracle_tape)
    secret n htr lowe actions.val (absI e1) (absS e2) [] hRA
  have h0 : ((0#usize : Std.Usize).val) = 0 := rfl
  simp only [h0, List.drop_zero] at ha1 ha2 hseen1 hseen2
  simp at ha2 hseen1 hseen2
  simp only [h0, List.drop_zero, deref_val, decide_eq_true_eq] at hn
  simp only [List.map_nil, idealPE, symPE] at hpf hseen1 hseen2 ha2
  rw [hseen1, hseen2]
  apply hpf
  · rw [← ha2]; simpa [absS] using hn
  · rw [← ha2]; simpa [absS] using hl

end

end examples.nsl
