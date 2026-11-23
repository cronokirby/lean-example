module

public import Examples.Nsl.Lawful
public import Examples.Nsl.Secrecy.Model
import Examples.Nsl.Secrecy.Step

/-! # Symbolic secrecy of NSL

With Lowe's check, no run of the protocol in the symbolic world encrypts a
message mentioning the secret to the adversary unless the session under attack
has the adversary as its peer. Without the check this is false (Lowe's attack,
see `Examples.Nsl.Attack`); the proof uses the check in exactly one place, when
an initiator accepts a message two that carries the secret of a responder.

The result is stated stepwise, for an adversary that picks each action after
seeing the previous responses:

* `SecInv` is the invariant (`Secrecy.Inv` from `Examples.Nsl.Secrecy.Model`
  on the symbolic world's state); `SymBounded k` bounds its counters by the
  number `k` of steps taken, which rules out overflow;
* `secInv_new`: both hold for a new symbolic world and no sessions;
* `secInv_step`: every action preserves them, for every tape (so the step
  never depends on the tape's nonce of the secret session);
* `SecInv.leaked`: under `SecInv`, a leak means the secret session exists and
  is not honest.

`secrecy_holds` combines them for a list of actions: the Rust property
`secrecy` with `lowe = true` returns `true`.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl

public section

variable {P T U Seed Coins Pk Sk Ct : Type _}

/-- The secrecy invariant of the symbolic world `env` with sessions `ss`
(see `Secrecy.Inv`). It depends only on the index of the secret session, the
leaked flag, the table and the sessions. -/
@[expose] def SecInv (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (ss : alloc.vec.Vec (Session Sym)) : Prop :=
  Secrecy.Inv env.secret.val env.leaked env.table.val ss.val

/-- After `k` steps every counter and vector of the symbolic world has at most
`k` entries. -/
@[expose] def SymBounded (k : Nat) (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (ss : alloc.vec.Vec (Session Sym)) : Prop :=
  env.count.val ≤ k ∧ env.oracle.count.val ≤ k ∧ env.table.length ≤ k ∧
    env.guesses.length ≤ k ∧ ss.length ≤ k

/-- The invariant holds at the start of a run. -/
theorem secInv_new (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins)
    (UI : Tape U Seed Coins) (tape : T) (oracle_tape : U) (secret : Std.Usize) :
    ∃ env, Symbolic.new E TI UI tape oracle_tape secret = ok env ∧
      SecInv env (alloc.vec.Vec.new _) ∧ SymBounded 0 env (alloc.vec.Vec.new _) := by
  simp only [Symbolic.new, RealOracle.new, bind_ok]
  refine ⟨_, rfl, ?_, ?_⟩
  · exact Secrecy.Inv.nil _
  · simp [SymBounded]

/-- **One step preserves the invariant.** With Lowe's check, every action
from a state satisfying `SecInv` after `k < Usize.max` steps returns (never
panics or overflows) and gives a state satisfying `SecInv`, with the counters
bounded by `k + 1`. The secret index and the tapes are unchanged. -/
theorem secInv_step {E : Pke P Seed Coins Pk Sk Ct} {TI : Tape T Seed Coins}
    {UI : Tape U Seed Coins} (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (k : Nat)
    (hk : k < Usize.max) (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (ss : alloc.vec.Vec (Session Sym)) (h : SecInv env ss) (hb : SymBounded k env ss)
    (a : Action Ct) :
    ∃ r env' ss', step (Symbolic.Insts.ExamplesNslEnvClause0_CtSym E TI UI) true env ss a =
        ok (r, env', ss') ∧
      SecInv env' ss' ∧ SymBounded (k + 1) env' ss' ∧ env'.secret = env.secret ∧
      env'.tape = env.tape ∧ env'.oracle.tape = env.oracle.tape := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  obtain ⟨⟨r, env', ss'⟩, heq, hp, hf, hl⟩ :=
    Secrecy.ok_of_spec (Secrecy.sym_step.spec hE hT hU env ss a (by omega) (by omega)
      (by omega) (by omega) (by omega))
  refine ⟨r, env', ss', heq, ?_, ?_, hf.secret, hf.tape, hf.oracle_tape⟩
  · unfold SecInv; rw [hf.secret]; exact h.step hp
  · have := hf.count; have := hf.oracle_count; have := hf.table; have := hf.guesses
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **A leak means the secret session is not honest.** Under `SecInv`, if
the secret leaked then session `env.secret` exists and `honest` returns
`false` for it: its peer is the adversary. -/
theorem SecInv.leaked {env : Symbolic P T U Seed Coins Pk Sk Ct}
    {ss : alloc.vec.Vec (Session Sym)} (h : SecInv env ss) (hl : env.leaked = true) :
    env.secret.val < ss.length ∧
      honest Sym.Insts.CoreMarkerCopy (alloc.vec.Vec.deref ss) env.secret = ok false := by
  unfold SecInv at h
  rw [hl] at h
  obtain ⟨s0, hs, hp⟩ := h.leaked
  have hlt : env.secret.val < ss.length := (List.getElem?_eq_some_iff.mp hs).1
  refine ⟨hlt, ?_⟩
  have hsp : honest Sym.Insts.CoreMarkerCopy (alloc.vec.Vec.deref ss) env.secret
      ⦃ b => b = false ⦄ := by
    unfold honest Session.peer
    step*
    have e : s = s0 := by
      have hd : (alloc.vec.Vec.deref ss).val = ss.val := by
        simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
      have h2 : (alloc.vec.Vec.deref ss).val[env.secret.val]? = some s0 := by rw [hd]; exact hs
      rw [List.getElem?_eq_getElem (by rw [hd]; exact hlt)] at h2
      rw [s_post]; exact Option.some.inj h2
    subst e
    cases s <;> simp_all [Secrecy.peerOf]
  obtain ⟨b, hb, rfl⟩ := Secrecy.ok_of_spec hsp
  exact hb

/-- The run loop keeps the invariant. -/
theorem run_loop_inv {E : Pke P Seed Coins Pk Sk Ct} {TI : Tape T Seed Coins}
    {UI : Tape U Seed Coins} (hE : E.Total) (hT : TI.Total) (hU : UI.Total)
    (actions : Slice (Action Ct)) (env : Symbolic P T U Seed Coins Pk Sk Ct)
    (ss : alloc.vec.Vec (Session Sym)) (seen : alloc.vec.Vec (Response Ct)) (i : Std.Usize)
    (hi : i.val ≤ actions.length) (h : SecInv env ss) (hb : SymBounded i.val env ss)
    (hseen : seen.length ≤ i.val) :
    run_loop (Symbolic.Insts.ExamplesNslEnvClause0_CtSym E TI UI) true env actions ss seen i
      ⦃ env' ss' _ => SecInv env' ss' ∧ env'.secret = env.secret ⦄ := by
  unfold run_loop
  dsimp only
  split
  · step
    obtain ⟨r, env', ss', heq, h', hb', hsec, -⟩ :=
      secInv_step hE hT hU i.val (by scalar_tac) env ss h hb a
    rw [heq]
    step*
    simp only [alloc.vec.Vec.length, seen1_post, List.length_append, List.length_singleton]
    scalar_tac
  · simpa using h
termination_by actions.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- **Symbolic secrecy of NSL.** With Lowe's check, for every total `Pke`
and total tapes, every tape, oracle tape, list of actions and secret session
index, the Rust property `secrecy` returns `true` (and does not panic): if
the symbolic run ever encrypts a message mentioning the secret nonce to the
adversary, then the secret session's peer is the adversary. -/
theorem secrecy_holds {E : Pke P Seed Coins Pk Sk Ct} {TI : Tape T Seed Coins}
    {UI : Tape U Seed Coins} (hE : E.Total) (hT : TI.Total) (hU : UI.Total) (tape : T)
    (oracle_tape : U) (actions : Slice (Action Ct)) (secret : Std.Usize) :
    secrecy E TI UI true tape oracle_tape actions secret = ok true := by
  obtain ⟨env, henv, h0, hb0⟩ := secInv_new E TI UI tape oracle_tape secret
  have hsp : secrecy E TI UI true tape oracle_tape actions secret ⦃ b => b = true ⦄ := by
    unfold secrecy run
    have hs : env.secret = secret := by
      simp [Symbolic.new, RealOracle.new] at henv
      rw [← henv]
    rw [henv]
    step with run_loop_inv hE hT hU actions env (alloc.vec.Vec.new _) (alloc.vec.Vec.new _)
      0#usize (by simp) h0 hb0 (by simp) as ⟨res, hinv, hsec⟩
    have hh := fun h => (SecInv.leaked hinv h).2
    rw [hsec, hs] at hh
    rcases res with ⟨env1, ss1, seen1⟩
    by_cases hl : env1.leaked = true
    · simp [hl, hh hl]
    · simp [hl]
  obtain ⟨b, hb, rfl⟩ := Secrecy.ok_of_spec hsp
  exact hb

end

end examples.nsl

