module

public import Examples.Nsl.Faithful.Step

/-! # Runs of the ideal and symbolic worlds

`prun` runs `pstep` over a list of actions. `run_loop_refines` shows that the
extracted `run_loop` computes it, and `prun_faithful` that the ideal and
symbolic models give the same responses unless the symbolic run leaked or
recorded `n` as a guess.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl

open Model Spec

namespace Model

/-- `pstep` over a list of actions: the final state and sessions and every response. -/
def prun {S N Ct : Type _} (pe : PEnv S N Ct) (lowe : Bool) :
    S → List (Session N) → List (Action Ct) → S × List (Session N) × List (Response Ct)
  | st, ss, [] => (st, ss, [])
  | st, ss, a :: acts =>
    match pstep pe lowe st ss a with
    | (r, st', ss') =>
      match prun pe lowe st' ss' acts with
      | (st'', ss'', rs) => (st'', ss'', r :: rs)

theorem prun_sym_mono {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t u : TapeF Seed Coins) (j : Std.Usize) (lowe : Bool) (b : SyA Ct) (s : List (Session Sym))
    (acts : List (Action Ct)) :
    b.guesses <+: (prun (symEnv F t u j) lowe b s acts).1.guesses ∧
      (b.leaked = true → (prun (symEnv F t u j) lowe b s acts).1.leaked = true) := by
  induction acts generalizing b s with
  | nil => simp [prun]
  | cons a acts ih =>
    obtain ⟨⟨r, b', s'⟩, hp⟩ : ∃ x, pstep (symEnv F t u j) lowe b s a = x := ⟨_, rfl⟩
    have hf := symStep_facts F t u j lowe b s a r b' s' hp
    have := ih b' s'
    simp only [prun, hp]
    exact ⟨hf.1.trans this.1, fun h => this.2 (hf.2.2.1 h)⟩

/-- **Faithfulness of the models.** Over any list of actions, the ideal model
gives the same responses as the symbolic one, unless the symbolic run leaked
or recorded `n` as a guess. -/
theorem prun_faithful {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t1 t2 u : TapeF Seed Coins) (j : Std.Usize) (n : Std.U64) (ht : TapeRel j n t1 t2)
    (lowe : Bool) (acts : List (Action Ct)) (a : IdA Ct) (b : SyA Ct) (s2 : List (Session Sym))
    (hR : RelA n a b)
    (hn : n ∉ (prun (symEnv F t2 u j) lowe b s2 acts).1.guesses)
    (hl : (prun (symEnv F t2 u j) lowe b s2 acts).1.leaked = false) :
    (prun (idealEnv F t1 u) lowe a (s2.map (sessMap (subst n))) acts).2.2 =
      (prun (symEnv F t2 u j) lowe b s2 acts).2.2 := by
  induction acts generalizing a b s2 with
  | nil => simp [prun]
  | cons act acts ih =>
    obtain ⟨⟨r2, b', s2'⟩, hp2⟩ : ∃ x, pstep (symEnv F t2 u j) lowe b s2 act = x := ⟨_, rfl⟩
    obtain ⟨⟨r1, a', s1'⟩, hp1⟩ :
        ∃ x, pstep (idealEnv F t1 u) lowe a (s2.map (sessMap (subst n))) act = x := ⟨_, rfl⟩
    simp only [prun, hp1, hp2] at hn hl ⊢
    have hm := prun_sym_mono F t2 u j lowe b' s2' acts
    have hn' : n ∉ b'.guesses := fun h => hn (hm.1.subset h)
    have hl' : b'.leaked = false := by
      cases h : b'.leaked
      · rfl
      · exact absurd (hm.2 h) (by simp [hl])
    obtain ⟨hR', hs', hr⟩ := rel_step F t1 t2 u j n ht lowe a b s2 act hR r1 a' s1' hp1 r2 b' s2' hp2 hn'
    subst hs'
    rw [hr hl', ih a' b' s2' hR' hn hl]

end Model

/-! ## The run loop computes `prun` -/

section Loop

variable {E Ct N S : Type _} (EI : Env E Ct N) (pe : PEnv S N Ct) (abs : E → S)
  (Inv : Nat → E → alloc.vec.Vec (Session N) → Prop)

theorem run_loop_refines
    (hstep : ∀ k e s a, k < Usize.max → Inv k e s →
      ∃ r e' s', nsl.step EI lowe e s a = ok (r, e', s') ∧
        pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ Inv (k + 1) e' s')
    (actions : Slice (Action Ct)) (e : E) (s : alloc.vec.Vec (Session N))
    (seen : alloc.vec.Vec (Response Ct)) (i : Std.Usize) (hi : i.val ≤ actions.length)
    (hinv : Inv i.val e s) (hseen : seen.length = i.val) :
    run_loop EI lowe e actions s seen i ⦃ e' s' seen' =>
      abs e' = (prun pe lowe (abs e) s.val (actions.val.drop i.val)).1 ∧
      s'.val = (prun pe lowe (abs e) s.val (actions.val.drop i.val)).2.1 ∧
      seen'.val = seen.val ++ (prun pe lowe (abs e) s.val (actions.val.drop i.val)).2.2 ∧
      ∃ k, Inv k e' s' ⦄ := by
  unfold run_loop
  dsimp only
  split
  · step
    obtain ⟨r, e', s', heq, hp, hinv'⟩ := hstep i.val e s a (by scalar_tac) hinv
    rw [heq]
    step*
    case hseen => simp_all [alloc.vec.Vec.length]
    rw [List.drop_eq_getElem_cons (by scalar_tac)]
    rw [i2_post] at e'_post e'_post1 e'_post2
    simp only [prun, ← a_post, hp]
    refine ⟨e'_post, e'_post1, by simp [e'_post2, seen1_post], _, e'_post3⟩
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp only [prun, List.append_nil]
    simp
    exact ⟨_, hinv⟩
termination_by actions.length - i.val
decreasing_by all_goals scalar_decr_tac

end Loop

end examples.nsl
