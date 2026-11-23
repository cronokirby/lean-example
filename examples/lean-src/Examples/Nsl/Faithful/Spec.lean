module

public import Examples.Nsl.Lawful
public import Examples.Nsl.Faithful.Model

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Spec

open Model

set_option linter.deprecated false

theorem natU_len {α : Type _} (s : alloc.vec.Vec α) : natU s.val.length = s.len := by
  rw [← natU_val s.len]; simp


/-! ## Lawful primitives as pure functions -/

section Prims

variable {P Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}

/-- A total ~Pke~ as pure functions. -/
def pkeF (hE : E.Total) : PkeF Seed Coins Pk Sk Ct where
  keygen s := Classical.choose (hE.keygen_ok s)
  enc pk m r := Classical.choose (hE.enc_ok pk m r)
  dec sk c := Classical.choose (hE.dec_ok sk c)

theorem keygen_eq (hE : E.Total) (s : Seed) :
    E.keygen s = ok (((pkeF hE).keygen s).1, ((pkeF hE).keygen s).2) :=
  Classical.choose_spec (hE.keygen_ok s)

theorem deref_val {α : Type _} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref, Slice.from, Slice.val, Data.ListN.ListN.from_to_inverse]
theorem enc_eq (hE : E.Total) (pk : Pk) (m : Msg Std.U64) (r : Coins) :
    E.enc pk m r = ok ((pkeF hE).enc pk m r) :=
  Classical.choose_spec (hE.enc_ok pk m r)
theorem dec_eq (hE : E.Total) (sk : Sk) (c : Ct) : E.dec sk c = ok ((pkeF hE).dec sk c) :=
  Classical.choose_spec (hE.dec_ok sk c)

variable {T : Type _} {TI : Tape T Seed Coins}

/-- A total tape as pure functions. -/
def tapeF (hT : TI.Total) (t : T) : TapeF Seed Coins where
  seed a := Classical.choose (hT.seed_ok t a)
  coins i := Classical.choose (hT.coins_ok t (natU i))
  nonce k := Classical.choose (hT.nonce_ok t k)

theorem seed_eq (hT : TI.Total) (t : T) (a : Std.U8) : TI.seed t a = ok ((tapeF hT t).seed a) :=
  Classical.choose_spec (hT.seed_ok t a)
theorem coins_eq (hT : TI.Total) (t : T) (i : Std.Usize) :
    TI.coins t i = ok ((tapeF hT t).coins i.val) := by
  have key : ∀ x y, x = y → TI.coins t x = ok (Classical.choose (hT.coins_ok t y)) := by
    intro x y h; subst h; exact Classical.choose_spec (hT.coins_ok t x)
  exact key _ _ (natU_val i).symm
theorem coins_natU (hT : TI.Total) (t : T) (i : Nat) :
    TI.coins t (natU i) = ok ((tapeF hT t).coins i) :=
  Classical.choose_spec (hT.coins_ok t (natU i))

theorem nonce_eq (hT : TI.Total) (t : T) (k : Std.Usize) :
    TI.nonce t k = ok ((tapeF hT t).nonce k) :=
  Classical.choose_spec (hT.nonce_ok t k)

/-- **Spec of ~lookup~ (loop)** -/
theorem lookup_loop_spec {N : Type _} (hE : E.Total) (table : Slice (Entry Ct N)) (b : Std.U8)
    (c : Ct) (i : Std.Usize) (hi : i.val ≤ table.length) :
    lookup_loop E.coremarkerCopyInst E.corecmpEqInst table b c i ⦃ r =>
      r = lookupF (table.val.drop i.val) b c ⦄ := by
  unfold lookup_loop
  simp only [hE.eq_ok]
  step*
  all_goals (try rw [List.drop_eq_getElem_cons (by scalar_tac)])
  all_goals simp_all [lookupF]
termination_by table.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step] theorem lookup_spec {N : Type _} (hE : E.Total) (I : core.marker.Copy N)
    (table : Slice (Entry Ct N)) (b : Std.U8) (c : Ct) :
    lookup E.coremarkerCopyInst E.corecmpEqInst I table b c ⦃ r => r = lookupF table.val b c ⦄ := by
  unfold lookup
  step with lookup_loop_spec hE table b c 0#usize (by scalar_tac)
  simp_all

theorem exists_of_spec {α : Type _} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ x, m = ok x ∧ p x := by
  cases m <;> simp_all

theorem eq_ok_of_spec {α : Type _} {m : Result α} {x : α} (h : m ⦃ r => r = x ⦄) : m = ok x := by
  cases m <;> simp_all

theorem lookup_eq {N : Type _} (hE : E.Total) (I : core.marker.Copy N)
    (table : Slice (Entry Ct N)) (b : Std.U8) (c : Ct) :
    lookup E.coremarkerCopyInst E.corecmpEqInst I table b c = ok (lookupF table.val b c) :=
  eq_ok_of_spec (lookup_spec hE I table b c)

end Prims

section Generic

variable {E Ct N S : Type _} (EI : Env E Ct N) (pe : PEnv S N Ct) (abs : E → S)
  (I RoomE RoomS : E → Prop)

/-- `nsl.step` computes `pstep` in any environment whose operations compute those
of `pe` (through `abs`), keep the invariant `I`, and have room to grow. -/
theorem step_refines
    (hnonce : ∀ e k, I e → EI.nonce e k ⦃ v e' => pe.nonce (abs e) k = (v, abs e') ∧ I e' ∧
      (RoomE e → RoomE e') ∧ (RoomS e → RoomS e') ⦄)
    (hsame : ∀ e x y, I e → RoomS e → EI.same e x y ⦃ b e' => pe.same (abs e) x y = (b, abs e') ∧
      I e' ∧ (RoomE e → RoomE e') ⦄)
    (henc : ∀ e d m, I e → RoomE e → EI.enc e d m ⦃ c e' => pe.enc (abs e) d m = (c, abs e') ∧
      I e' ∧ (RoomS e → RoomS e') ⦄)
    (hdec : ∀ e b c, I e → EI.dec e b c ⦃ o e' => pe.dec (abs e) b c = (o, abs e') ∧ I e' ∧
      (RoomE e → RoomE e') ∧ (RoomS e → RoomS e') ⦄)
    (lowe : Bool) (e : E) (s : alloc.vec.Vec (Session N)) (a : Action Ct)
    (hI : I e) (hE : RoomE e) (hS : RoomS e) (hs : s.length < Usize.max) :
    nsl.step EI lowe e s a ⦃ r e' s' =>
      pstep pe lowe (abs e) s.val a = (r, abs e', s'.val) ∧ I e' ⦄ := by
  unfold nsl.step
  cases a with
  | Start o p =>
    simp only
    split
    · simp_all [pstep]
    · step*
      simp_all [pstep, natU_len]
  | Respond o m =>
    simp only
    split
    · simp_all [pstep]
    · step* <;> simp_all [pstep, natU_len]
  | Deliver k m =>
    simp only
    split
    · simp only [pstep]; rw [dif_neg (by scalar_tac)]; simp_all
    · step* <;> (simp only [pstep]; rw [dif_pos (by scalar_tac)]) <;> split <;>
        first | (simp_all [natU_len]; done) | grind

end Generic


/-! ## The ideal world -/

section Ideal

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}
  (hE : E.Total) (hT : TI.Total) (hU : UI.Total)

/-- ~World~ over ~IdealOracle~ as an ~Env~. -/
abbrev idealInst (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins) (UI : Tape U Seed Coins) :=
  World.Insts.ExamplesNslEnvClause0_CtU64 E TI (IdealOracle.Insts.ExamplesNslOracle E UI)

/-- The abstract state of the ideal world. -/
def absI (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) : IdA Ct :=
  ⟨e.count.val, e.oracle.real.count.val, e.oracle.table.val⟩

/-- Room for one more encryption in the ideal world. -/
def roomI (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) : Prop :=
  e.count.val < Usize.max ∧ e.oracle.real.count.val < Usize.max ∧ e.oracle.table.length < Usize.max

/-- The ideal world's tapes are ~t~ and ~u~. -/
def frameI (t : T) (u : U) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) : Prop :=
  e.tape = t ∧ e.oracle.real.tape = u

/-- The pure model of the ideal world with tapes ~t~ and ~u~. -/
def idealPE (t : T) (u : U) : PEnv (IdA Ct) Std.U64 Ct :=
  idealEnv (pkeF hE) (tapeF hT t) (tapeF hU u)

theorem ideal_nonce (t : T) (u : U) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct))
    (k : Std.Usize) (hI : frameI t u e) :
    (idealInst E TI UI).nonce e k ⦃ v e' => (idealPE hE hT hU t u).nonce (absI e) k = (v, absI e') ∧
      frameI t u e' ∧ (roomI e → roomI e') ∧ (True → True) ⦄ := by
  obtain ⟨rfl, rfl⟩ := hI
  simp [World.Insts.ExamplesNslEnvClause0_CtU64.nonce, nonce_eq hT, idealPE, idealEnv, frameI]

theorem ideal_same (t : T) (u : U) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct))
    (x y : Std.U64) (hI : frameI t u e) (_ : True) :
    (idealInst E TI UI).same e x y ⦃ b e' => (idealPE hE hT hU t u).same (absI e) x y = (b, absI e') ∧
      frameI t u e' ∧ (roomI e → roomI e') ⦄ := by
  simp_all [World.Insts.ExamplesNslEnvClause0_CtU64.same, idealPE, idealEnv]

theorem ideal_dec (t : T) (u : U) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct))
    (b : Std.U8) (c : Ct) (hI : frameI t u e) :
    (idealInst E TI UI).dec e b c ⦃ o e' => (idealPE hE hT hU t u).dec (absI e) b c = (o, absI e') ∧
      frameI t u e' ∧ (roomI e → roomI e') ∧ (True → True) ⦄ := by
  obtain ⟨rfl, hu⟩ := hI
  simp only [World.Insts.ExamplesNslEnvClause0_CtU64.dec, IdealOracle.Insts.ExamplesNslOracle.dec,
    RealOracle.Insts.ExamplesNslOracle.dec, seed_eq hU, keygen_eq hE, dec_eq hE]
  step*
  subst_vars
  split <;> (repeat' split) <;> simp_all [deref_val, idealPE, idealEnv, absI, frameI]

theorem ideal_enc (t : T) (u : U) (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct))
    (d : Std.U8) (m : Msg Std.U64) (hI : frameI t u e) (hr : roomI e) :
    (idealInst E TI UI).enc e d m ⦃ c e' => (idealPE hE hT hU t u).enc (absI e) d m = (c, absI e') ∧
      frameI t u e' ∧ (True → True) ⦄ := by
  obtain ⟨rfl, hu⟩ := hI
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [World.Insts.ExamplesNslEnvClause0_CtU64.enc, IdealOracle.Insts.ExamplesNslOracle.enc,
    RealOracle.Insts.ExamplesNslOracle.enc, RealOracle.Insts.ExamplesNslOracle.pk,
    seed_eq hT, seed_eq hU, keygen_eq hE, coins_eq hT, coins_eq hU, enc_eq hE]
  split <;> (repeat' split) <;> step* <;> simp_all [deref_val, idealPE, idealEnv, absI, frameI, natU_val]

theorem concretize_eq (m : Msg Sym) : concretize m = ok (concF m) := by
  rcases m with ⟨a, x⟩ | ⟨a, b, x⟩ | a <;> (try cases a) <;> (try cases b) <;> rfl

theorem symbolize_eq (m : Msg Std.U64) : symbolize m = ok (msgMap Sym.Val m) := by
  cases m <;> rfl

/-- **The ideal world computes ~idealEnv~.** -/
theorem ideal_step (t : T) (u : U) (lowe : Bool)
    (e : World P T (IdealOracle P U Seed Coins Pk Sk Ct)) (s : alloc.vec.Vec (Session Std.U64))
    (a : Action Ct) (hI : frameI t u e) (hr : roomI e) (hs : s.length < Usize.max) :
    nsl.step (idealInst E TI UI) lowe e s a ⦃ r e' s' =>
      pstep (idealPE hE hT hU t u) lowe (absI e) s.val a = (r, absI e', s'.val) ∧ frameI t u e' ⦄ :=
  step_refines (idealInst E TI UI) (idealPE hE hT hU t u) absI (frameI t u) roomI (fun _ => True)
    (ideal_nonce hE hT hU t u) (ideal_same hE hT hU t u) (fun e d m h1 h2 => ideal_enc hE hT hU t u e d m h1 h2)
    (ideal_dec hE hT hU t u) lowe e s a hI hr trivial hs

end Ideal

/-! ## The symbolic world -/

section Sym

variable {P T U Seed Coins Pk Sk Ct : Type _} {E : Pke P Seed Coins Pk Sk Ct}
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins}
  (hE : E.Total) (hT : TI.Total) (hU : UI.Total)

/-- ~Symbolic~ as an ~Env~. -/
abbrev symInst (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins) (UI : Tape U Seed Coins) :=
  Symbolic.Insts.ExamplesNslEnvClause0_CtSym E TI UI

/-- The abstract state of the symbolic world. -/
def absS (e : Symbolic P T U Seed Coins Pk Sk Ct) : SyA Ct :=
  ⟨e.count.val, e.oracle.count.val, e.table.val, e.guesses.val, e.leaked⟩

/-- Room for one more encryption in the symbolic world. -/
def roomSE (e : Symbolic P T U Seed Coins Pk Sk Ct) : Prop :=
  e.count.val < Usize.max ∧ e.oracle.count.val < Usize.max ∧ e.table.length < Usize.max

/-- Room for one more guess in the symbolic world. -/
def roomSS (e : Symbolic P T U Seed Coins Pk Sk Ct) : Prop :=
  e.guesses.length < Usize.max

/-- The symbolic world's tapes are ~t~ and ~u~ and its secret is ~j~. -/
def frameS (t : T) (u : U) (j : Std.Usize) (e : Symbolic P T U Seed Coins Pk Sk Ct) : Prop :=
  e.tape = t ∧ e.oracle.tape = u ∧ e.secret = j

/-- The pure model of the symbolic world. -/
def symPE (t : T) (u : U) (j : Std.Usize) : PEnv (SyA Ct) Sym Ct :=
  symEnv (pkeF hE) (tapeF hT t) (tapeF hU u) j

theorem sym_nonce (t : T) (u : U) (j : Std.Usize) (e : Symbolic P T U Seed Coins Pk Sk Ct)
    (k : Std.Usize) (hI : frameS t u j e) :
    (symInst E TI UI).nonce e k ⦃ v e' => (symPE hE hT hU t u j).nonce (absS e) k = (v, absS e') ∧
      frameS t u j e' ∧ (roomSE e → roomSE e') ∧ (roomSS e → roomSS e') ⦄ := by
  obtain ⟨rfl, rfl, rfl⟩ := hI
  simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.nonce]
  split <;> simp_all [nonce_eq hT, symPE, symEnv, frameS]

theorem sym_same (t : T) (u : U) (j : Std.Usize) (e : Symbolic P T U Seed Coins Pk Sk Ct)
    (x y : Sym) (hI : frameS t u j e) (hr : roomSS e) :
    (symInst E TI UI).same e x y ⦃ b e' => (symPE hE hT hU t u j).same (absS e) x y = (b, absS e') ∧
      frameS t u j e' ∧ (roomSE e → roomSE e') ⦄ := by
  simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.same]
  simp only [roomSS] at hr
  split <;> split <;> step* <;> simp_all [symPE, symEnv, absS, frameS, roomSE]

theorem sym_dec (t : T) (u : U) (j : Std.Usize) (e : Symbolic P T U Seed Coins Pk Sk Ct)
    (b : Std.U8) (c : Ct) (hI : frameS t u j e) :
    (symInst E TI UI).dec e b c ⦃ o e' => (symPE hE hT hU t u j).dec (absS e) b c = (o, absS e') ∧
      frameS t u j e' ∧ (roomSE e → roomSE e') ∧ (roomSS e → roomSS e') ⦄ := by
  obtain ⟨rfl, hu, rfl⟩ := hI
  simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.dec,
    RealOracle.Insts.ExamplesNslOracle.dec, seed_eq hU, keygen_eq hE, dec_eq hE, symbolize_eq,
    lookup_eq hE, deref_val, Std.bind_ok]
  subst_vars
  rcases hl : lookupF e.table.val b c with _ | msg
  all_goals simp only [hl]
  · rcases hk : (pkeF hE).keygen ((tapeF hU e.oracle.tape).seed b) with ⟨pk, sk⟩
    rcases hd : (pkeF hE).dec sk c with _ | m <;> simp_all [symPE, symEnv, absS, frameS]
  · simp_all [symPE, symEnv, absS, frameS]

theorem sym_enc (t : T) (u : U) (j : Std.Usize) (e : Symbolic P T U Seed Coins Pk Sk Ct)
    (d : Std.U8) (m : Msg Sym) (hI : frameS t u j e) (hr : roomSE e) :
    (symInst E TI UI).enc e d m ⦃ c e' => (symPE hE hT hU t u j).enc (absS e) d m = (c, absS e') ∧
      frameS t u j e' ∧ (roomSS e → roomSS e') ⦄ := by
  obtain ⟨rfl, hu, rfl⟩ := hI
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [Symbolic.Insts.ExamplesNslEnvClause0_CtSym.enc,
    RealOracle.Insts.ExamplesNslOracle.enc, RealOracle.Insts.ExamplesNslOracle.pk,
    seed_eq hT, seed_eq hU, keygen_eq hE, coins_eq hT, coins_eq hU, enc_eq hE]
  split
  · simp only [concretize_eq, Std.bind_ok]
    split <;> step* <;> simp_all [symPE, symEnv, absS, frameS, roomSS, natU_val]
  · step* <;> simp_all [symPE, symEnv, absS, frameS, roomSS, natU_val]

/-- **The symbolic world computes ~symEnv~.** -/
theorem sym_step (t : T) (u : U) (j : Std.Usize) (lowe : Bool)
    (e : Symbolic P T U Seed Coins Pk Sk Ct) (s : alloc.vec.Vec (Session Sym))
    (a : Action Ct) (hI : frameS t u j e) (hr : roomSE e) (hg : roomSS e)
    (hs : s.length < Usize.max) :
    nsl.step (symInst E TI UI) lowe e s a ⦃ r e' s' =>
      pstep (symPE hE hT hU t u j) lowe (absS e) s.val a = (r, absS e', s'.val) ∧
        frameS t u j e' ⦄ :=
  step_refines (symInst E TI UI) (symPE hE hT hU t u j) absS (frameS t u j) roomSE roomSS
    (sym_nonce hE hT hU t u j) (sym_same hE hT hU t u j) (sym_enc hE hT hU t u j)
    (sym_dec hE hT hU t u j) lowe e s a hI hr hg hs

end Sym

end examples.nsl.Spec
