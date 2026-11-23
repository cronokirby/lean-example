module

public import Examples.Nsl.Probability
public import Examples.Nsl.Faithful.Step
public import Examples.Nsl.Secrecy

/-! # The ideal secrecy game and the symbolic world, adaptively

Fix a session index `j`. `badList` runs the secrecy game's adversary against
the symbolic world with secret session `j`, on the tape with session `j`'s
nonce erased, and collects every value the secret was compared with, plus the
adversary's final guess. It stops early if the symbolic world leaks the
secret or a step fails.

`ideal_win_bad`: if the adversary wins the ideal secrecy game (with Lowe's
fix) by naming session `j`, then session `j`'s nonce is in `badList` for `j`.
The list has at most `q + 1` entries (`badList_length`) and does not depend on
session `j`'s nonce (it is computed from the erased tape), which is what the
counting argument needs.

The proof couples the ideal game and the symbolic run step by step
(`faithful_step`): as long as the symbolic run neither compared the secret
with the actual nonce `n` nor leaked, both give the adversary the same
responses, so the adversary is in the same state in both. If the symbolic run
leaks, the symbolic secrecy invariant (`SecInv`, from
`Examples.Nsl.Secrecy`) says session `j`'s peer is the adversary; the ideal
run has the same peer for session `j` and never changes it, so the adversary
cannot win by naming `j`.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Game

open Model Spec

set_option linter.deprecated false

theorem bind_inv {α β : Type _} {x : Result α} {f : α → Result β} {y : β}
    (h : (do let a ← x; f a) = ok y) : ∃ a, x = ok a ∧ f a = ok y := by
  cases x <;> simp_all

variable {P Seed Coins Pk Sk Ct A : Type} {q : Nat}

/-- The tape `t` with session `j`'s nonce set to 0. -/
def erase (j : Fin q) (t : GameTape Seed Coins q) : GameTape Seed Coins q :=
  { t with nonces := Function.update t.nonces j 0#u64 }

/-- The ideal oracle built from the oracle tape `ot` (what `IdealOracle.new` returns). -/
def idealOracle (P : Type) (ot : GameTape Seed Coins q) :
    IdealOracle P (GameTape Seed Coins q) Seed Coins Pk Sk Ct :=
  { real := { tape := ot, count := 0#usize, pke := () }, table := alloc.vec.Vec.new _ }

/-- The symbolic world with tape `t`, oracle tape `ot` and secret session `j`
(what `Symbolic.new` returns). -/
def symWorld (P : Type) (t ot : GameTape Seed Coins q) (j : Std.Usize) :
    Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct :=
  { tape := t, oracle := { tape := ot, count := 0#usize, pke := () }, secret := j,
    table := alloc.vec.Vec.new _, count := 0#usize, guesses := alloc.vec.Vec.new _,
    leaked := false }

/-- The start of the secrecy game: the adversary's key pair, every public key,
and the adversary's `start`. -/
def gameStart {T O : Type} (E : Pke P Seed Coins Pk Sk Ct) (TI : Tape T Seed Coins)
    (OI : Oracle O Pk Ct) (Adv : Adversary A Pk Sk Ct) (t : T) (o : O) (adv : A) : Result A := do
  let t0 ← TI.seed t ADVERSARY
  let (pk, sk) ← E.keygen t0
  let pks ← alloc.vec.Vec.push (alloc.vec.Vec.new Pk) pk
  let pks1 ← secrecy_game_loop0 OI o pks 1#usize
  Adv.start adv (alloc.vec.Vec.deref pks1) sk

/-- One round against the symbolic world: the adversary's next action and the
step it causes (with Lowe's fix). -/
def symRound (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (e : Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct)
    (s : alloc.vec.Vec (Session Sym)) (last : Response Ct) :
    Result (A × Response Ct ×
      Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct ×
      alloc.vec.Vec (Session Sym)) := do
  let (act, adv1) ← Adv.next adv last
  let (r, e', s') ← step (symInst E (gameTape Seed Coins q) (gameTape Seed Coins q)) true e s act
  ok (adv1, r, e', s')

open Classical in
/-- Runs the adversary for `fuel` more rounds against the symbolic world and
returns the values the secret was compared with, plus the final guess if the
run finished without leaking. It stops early at a leak or a failure. -/
def symRun (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) :
    Nat → A → Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct →
      alloc.vec.Vec (Session Sym) → Response Ct → List Std.U64
  | 0, adv, e, _, last =>
    if e.leaked then e.guesses.val
    else if h : ∃ x, Adv.guess adv last = ok x then h.choose.1.2 :: e.guesses.val
    else e.guesses.val
  | f + 1, adv, e, s, last =>
    if e.leaked then e.guesses.val
    else if h : ∃ x, symRound E Adv adv e s last = ok x then
      symRun E Adv f h.choose.1 h.choose.2.2.1 h.choose.2.2.2 h.choose.2.1
    else e.guesses.val

open Classical in
/-- The values the adversary's run against the symbolic world (secret session
`j`, tape `t`, oracle tape `ot`) compared with the secret, and its final guess. -/
def badList (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A) (q : Std.Usize)
    (j : Std.Usize) (t ot : GameTape Seed Coins q.val) : List Std.U64 :=
  if h : ∃ a1, gameStart E (gameTape Seed Coins q.val)
      (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q.val)) Adv t
      (idealOracle P ot) adv = ok a1 then
    symRun E Adv q.val h.choose (symWorld P t ot j) (alloc.vec.Vec.new _) Response.Rejected
  else []

/-! ## Facts about the symbolic run -/

theorem symRound_inv {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (k : Nat) (hk : k < Usize.max) (adv : A)
    (e : Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct)
    (s : alloc.vec.Vec (Session Sym)) (last : Response Ct) (hb : SymBnd k e s) (x)
    (h : symRound E Adv adv e s last = ok x) :
    SymBnd (k + 1) x.2.2.1 x.2.2.2 ∧ e.guesses.val <+: x.2.2.1.guesses.val ∧
      x.2.2.1.guesses.val.length ≤ e.guesses.val.length + 1 := by
  unfold symRound at h
  obtain ⟨⟨act, adv1⟩, -, h⟩ := bind_inv h
  obtain ⟨⟨r, e', s'⟩, hs, h⟩ := bind_inv h
  have hx : x = (adv1, r, e', s') := by
    simpa using h.symm
  subst hx
  obtain ⟨r0, e0, s0, heq, hp, -, hb'⟩ := sym_hstep hE (gameTape_total Seed Coins q)
    (gameTape_total Seed Coins q) e.tape e.oracle.tape e.secret true k e s act hk ⟨⟨rfl, rfl, rfl⟩, hb⟩
  rw [hs] at heq
  simp only [Result.ok.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hf := symStep_facts _ _ _ _ _ _ _ _ _ _ _ hp
  simp only [absS] at hf
  exact ⟨hb', hf.1, hf.2.1⟩

theorem symRun_facts {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (fuel : Nat) : ∀ (k : Nat) (adv : A)
    (e : Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct)
    (s : alloc.vec.Vec (Session Sym)) (last : Response Ct), SymBnd k e s → k + fuel ≤ Usize.max →
    (∀ x ∈ e.guesses.val, x ∈ symRun E Adv fuel adv e s last) ∧
      (symRun E Adv fuel adv e s last).length ≤ e.guesses.val.length + fuel + 1 := by
  induction fuel with
  | zero =>
    intro k adv e s last _ _
    simp only [symRun]
    split_ifs <;> exact ⟨fun x hx => by simp [hx], by simp⟩
  | succ f ih =>
    intro k adv e s last hb hk
    simp only [symRun]
    split_ifs with hl hx
    · exact ⟨fun x hx => hx, by omega⟩
    · have hspec := hx.choose_spec
      generalize hx.choose = x at hspec ⊢
      obtain ⟨hb', hpre, hlen⟩ := symRound_inv Adv hE k (by omega) adv e s last hb x hspec
      obtain ⟨ih1, ih2⟩ := ih (k + 1) x.1 x.2.2.1 x.2.2.2 x.2.1 hb' (by omega)
      exact ⟨fun y hy => ih1 y (hpre.subset hy), by omega⟩
    · exact ⟨fun x hx => hx, by omega⟩

/-! ## Facts about the ideal run -/

theorem idealBnd_of_related {T1 T2 U : Type} {TI1 : Tape T1 Seed Coins} {TI2 : Tape T2 Seed Coins}
    {j : Std.Usize} {n : Std.U64} {k : Nat}
    {e1 : World P T1 (IdealOracle P U Seed Coins Pk Sk Ct)} {s1 : alloc.vec.Vec (Session Std.U64)}
    {e2 : Symbolic P T2 U Seed Coins Pk Sk Ct} {s2 : alloc.vec.Vec (Session Sym)}
    (hR : Related TI1 TI2 j n e1 s1 e2 s2) (hb : SymBnd k e2 s2) : IdealBnd k e1 s1 := by
  obtain ⟨-, -, -, -, -, -, hc, ho, ht, hs⟩ := hR
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  simp only [alloc.vec.Vec.length] at *
  refine ⟨by rw [hc]; exact b1, by rw [ho]; exact b2, ?_, ?_⟩
  · simp only [alloc.vec.Vec.length, ht, List.length_map]; exact b3
  · simp only [alloc.vec.Vec.length, hs, List.length_map]; exact b5

theorem honest_spec {N : Type} (I : core.marker.Copy N) (ss : alloc.vec.Vec (Session N))
    (k : Std.Usize) :
    honest I (alloc.vec.Vec.deref ss) k ⦃ b =>
      (b = true ↔ ∃ h : k.val < ss.val.length, peerF ss.val[k.val] ≠ ADVERSARY) ⦄ := by
  unfold honest
  have hd : (alloc.vec.Vec.deref ss).val = ss.val := deref_val ss
  dsimp only
  split
  · step
    have hp : Session.peer I s = ok (peerF s) := by cases s <;> rfl
    rw [hp]
    simp only [bind_ok, WP.spec_ok]
    have hk : k.val < ss.val.length := by rw [← hd]; scalar_tac
    simp only [hk, exists_true_left]
    rw [s_post]
    simp [hd]
  · simp only [WP.spec_ok]
    have : ¬ k.val < ss.val.length := by rw [← hd]; scalar_tac
    simp [this]


theorem add_one_val {i i1 : Std.Usize} (h : i + 1#usize = ok i1) (hi : i.val < Usize.max) :
    i1.val = i.val + 1 := by
  have := Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
  rw [h] at this
  simpa using this

/-- A new session's nonce is the environment's nonce for its index; old
sessions keep their nonces. -/
theorem pstep_nonces {S N Ct : Type _} (pe : PEnv S N Ct) (lowe : Bool) (st : S)
    (ss : List (Session N)) (a : Action Ct) (r : Response Ct) (st' : S) (ss' : List (Session N))
    (h : pstep pe lowe st ss a = (r, st', ss')) (v : N)
    (hv : ∀ st0, (pe.nonce st0 (natU ss.length)).1 = v) :
    ∀ k (hk : k < ss'.length), (∃ h : k < ss.length, nonceF ss'[k] = nonceF ss[k]) ∨
      (k = ss.length ∧ nonceF ss'[k] = v) := by
  cases a <;> simp only [pstep] at h <;> (repeat' split at h) <;> simp at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> simp_all [List.getElem_append_left, List.getElem_set] <;>
    grind [nonceF]

/-- In the symbolic world the secret session's nonce is the secret. -/
def NonceInv (j : Nat) (ss : List (Session Sym)) : Prop :=
  ∀ h : j < ss.length, nonceF ss[j] = Sym.Secret

theorem nonceInv_step {Seed Coins Pk Sk : Type} (F : PkeF Seed Coins Pk Sk Ct) (t u : TapeF Seed Coins)
    (j : Std.Usize) (lowe : Bool) (b : SyA Ct) (ss : List (Session Sym)) (a : Action Ct)
    (r : Response Ct) (b' : SyA Ct) (ss' : List (Session Sym))
    (h : pstep (symEnv F t u j) lowe b ss a = (r, b', ss')) (hinv : NonceInv j.val ss) :
    NonceInv j.val ss' := by
  intro hj
  rcases pstep_nonces _ _ _ _ _ _ _ _ h
    (if natU ss.length = j then Sym.Secret else Sym.Val (t.nonce (natU ss.length)))
    (fun _ => rfl) j.val hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]; exact hinv h1
  · rw [h2]
    have : natU ss.length = j := by rw [← h1, natU_val]
    simp [this]

/-- Every encryption ~gameTape~ is total. -/
theorem gT (q : Nat) : (gameTape Seed Coins q).Total := gameTape_total Seed Coins q

/-- **The ideal run alone.** It makes at most ~q~ sessions and never changes a
session's peer. -/
theorem ideal_alone {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (lowe : Bool) (qu : Std.Usize) (fuel : Nat) :
    ∀ (i : Std.Usize) (adv : A)
      (e1 : World P (GameTape Seed Coins q)
        (IdealOracle P (GameTape Seed Coins q) Seed Coins Pk Sk Ct))
      (s1 : alloc.vec.Vec (Session Std.U64)) (last : Response Ct) res,
      i.val + fuel = qu.val → IdealBnd i.val e1 s1 →
      secrecy_game_loop1 E (gameTape Seed Coins q)
        (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) Adv lowe adv qu e1 s1 last i =
        ok res →
      res.2.1.val.length ≤ qu.val ∧
        ∀ j (hj : j < s1.val.length), peerF s1.val[j] = ADVERSARY →
          ∃ h : j < res.2.1.val.length, peerF res.2.1.val[j] = ADVERSARY := by
  induction fuel with
  | zero =>
    intro i adv e1 s1 last res hi hb h
    unfold secrecy_game_loop1 at h
    rw [if_neg (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    obtain ⟨-, -, -, b4⟩ := hb
    simp only [alloc.vec.Vec.length] at b4
    dsimp only
    exact ⟨by omega, fun j hj hp => ⟨hj, hp⟩⟩
  | succ f ih =>
    intro i adv e1 s1 last res hi hb h
    unfold secrecy_game_loop1 at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨⟨act, adv1⟩, -, h⟩ := bind_inv h
    obtain ⟨⟨r1, e1', s1'⟩, hs, h⟩ := bind_inv h
    obtain ⟨i1, hi1, h⟩ := bind_inv h
    have hiv := add_one_val hi1 (by scalar_tac)
    obtain ⟨r0, e0, s0, heq, hb', -, -, hpeer⟩ :=
      ideal_step_ok hE (gT q) (gT q) lowe i.val (by scalar_tac) e1 s1 hb act
    rw [hs] at heq
    simp only [Result.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨ih1, ih2⟩ := ih i1 adv1 e1' s1' r1 res (by omega) (by rw [hiv]; exact hb') h
    refine ⟨ih1, fun j hj hp => ?_⟩
    obtain ⟨hj', hp'⟩ := hpeer j hj
    exact ih2 j hj' (by rw [hp', hp])


/-- The secrecy game's final state wins by naming session ~j~: the adversary's
guess names ~j~, session ~j~ exists with an honest peer, and the guessed value
is its nonce. -/
def WinAt (Adv : Adversary A Pk Sk Ct) (j : Nat)
    (res : A × alloc.vec.Vec (Session Std.U64) × Response Ct) : Prop :=
  ∃ k g a3, Adv.guess res.1 res.2.2 = ok ((k, g), a3) ∧ k.val = j ∧
    ∃ h : j < res.2.1.val.length, peerF res.2.1.val[j] ≠ ADVERSARY ∧ nonceF res.2.1.val[j] = g

theorem subst_secret (n : Std.U64) : subst n Sym.Secret = n := rfl

/-- **The coupling.** From related ideal and symbolic states (secret session
~jU~, actual nonce ~n~) with the same adversary state and last response, if the
ideal loop ends in a state that wins by naming ~jU~, then ~n~ is among the
values ~symRun~ returns. -/
theorem couple {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (qu jU : Std.Usize) (n : Std.U64) (fuel : Nat) :
    ∀ (i : Std.Usize) (adv : A)
      (e1 : World P (GameTape Seed Coins q)
        (IdealOracle P (GameTape Seed Coins q) Seed Coins Pk Sk Ct))
      (s1 : alloc.vec.Vec (Session Std.U64)) (last : Response Ct)
      (e2 : Symbolic P (GameTape Seed Coins q) (GameTape Seed Coins q) Seed Coins Pk Sk Ct)
      (s2 : alloc.vec.Vec (Session Sym)) res,
      i.val + fuel = qu.val →
      Related (gameTape Seed Coins q) (gameTape Seed Coins q) jU n e1 s1 e2 s2 →
      SymBnd i.val e2 s2 → SecInv e2 s2 → e2.leaked = false → NonceInv jU.val s2.val →
      secrecy_game_loop1 E (gameTape Seed Coins q)
        (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) Adv true adv qu e1 s1 last i =
        ok res →
      WinAt Adv jU.val res →
      n ∈ symRun E Adv fuel adv e2 s2 last := by
  induction fuel with
  | zero =>
    intro i adv e1 s1 last e2 s2 res hi hR hb hinv hl hnon h hw
    unfold secrecy_game_loop1 at h
    rw [if_neg (by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    subst h
    obtain ⟨k, g, a3, hg, -, hj, -, hng⟩ := hw
    simp only [symRun, hl, Bool.false_eq_true, if_false]
    have hx : ∃ x, Adv.guess adv last = ok x := ⟨_, hg⟩
    rw [dif_pos hx]
    have hc := hx.choose_spec
    generalize hx.choose = x at hc ⊢
    simp only at hg hj hng
    rw [hg] at hc
    simp only [Result.ok.injEq] at hc
    rw [← hc]
    have hs1 := hR.2.2.2.2.2.2.2.2.2
    have hj2 : jU.val < s2.val.length := by
      have := hj; simp only [hs1, List.length_map] at this; exact this
    have h1 : nonceF s1.val[jU.val] = n := by
      simp only [hs1, List.getElem_map, nonceF_sessMap, hnon hj2, subst_secret]
    rw [← hng, h1]
    exact List.mem_cons_self
  | succ f ih =>
    intro i adv e1 s1 last e2 s2 res hi hR hb hinv hl hnon h hw
    unfold secrecy_game_loop1 at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨⟨act, adv1⟩, hnext, h⟩ := bind_inv h
    obtain ⟨⟨r1, e1', s1'⟩, hs, h⟩ := bind_inv h
    obtain ⟨i1, hi1, h⟩ := bind_inv h
    have hiv := add_one_val hi1 (by scalar_tac)
    have hk : i.val < Usize.max := by scalar_tac
    obtain ⟨r1', e1'', s1'', r2, e2', s2', heq1, heq2, hb', hpre, -, hrel⟩ :=
      faithful_step hE (gT q) (gT q) (gT q) true jU n i.val hk e1 s1 e2 s2 hR hb act
    rw [hs] at heq1
    simp only [Result.ok.injEq, Prod.mk.injEq] at heq1
    obtain ⟨rfl, rfl, rfl⟩ := heq1
    obtain ⟨r3, e3, s3, heq3, hinv', -⟩ :=
      secInv_step hE (gT q) (gT q) i.val hk e2 s2 hinv hb act
    rw [heq2] at heq3
    simp only [Result.ok.injEq, Prod.mk.injEq] at heq3
    obtain ⟨rfl, rfl, rfl⟩ := heq3
    obtain ⟨r4, e4, s4, heq4, hp4, -⟩ := sym_hstep hE (gT q) (gT q) e2.tape e2.oracle.tape
      e2.secret true i.val e2 s2 act hk ⟨⟨rfl, rfl, rfl⟩, hb⟩
    rw [heq2] at heq4
    simp only [Result.ok.injEq, Prod.mk.injEq] at heq4
    obtain ⟨rfl, rfl, rfl⟩ := heq4
    have hsec : e2.secret = jU := hR.2.2.2.2.2.1
    have hnon' : NonceInv jU.val s2'.val := by
      rw [← hsec]; exact nonceInv_step _ _ _ _ _ _ _ _ _ _ _ hp4 (by rw [hsec]; exact hnon)
    simp only [symRun, hl, Bool.false_eq_true, if_false]
    have hround : symRound E Adv adv e2 s2 last = ok (adv1, r2, e2', s2') := by
      simp [symRound, hnext, heq2]
    have hx : ∃ x, symRound E Adv adv e2 s2 last = ok x := ⟨_, hround⟩
    rw [dif_pos hx]
    have hc := hx.choose_spec
    generalize hx.choose = x at hc ⊢
    rw [hround] at hc
    simp only [Result.ok.injEq] at hc
    rw [← hc]
    by_cases hn : n ∈ e2'.guesses.val
    · exact (symRun_facts Adv hE f (i.val + 1) adv1 e2' s2' r2 hb' (by scalar_tac)).1 n hn
    · obtain ⟨hR', hr⟩ := hrel hn
      cases hl' : e2'.leaked
      · have := hr hl'
        subst this
        exact ih i1 adv1 e1' s1' r1 e2' s2' res (by omega) hR' (by rw [hiv]; exact hb') hinv' hl'
          hnon' h hw
      · exfalso
        obtain ⟨hjl, hhon⟩ := SecInv.leaked hinv' hl'
        have hpf := honest_spec Sym.Insts.CoreMarkerCopy s2' e2'.secret
        rw [hhon] at hpf
        simp only [WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_not] at hpf
        have hsec' : e2'.secret = jU := hR'.2.2.2.2.2.1
        rw [hsec'] at hjl hpf
        have hs1 := hR'.2.2.2.2.2.2.2.2.2
        have hj1 : jU.val < s1'.val.length := by simp only [hs1, List.length_map]; exact hjl
        have hp1 : peerF s1'.val[jU.val] = ADVERSARY := by
          simp only [hs1, List.getElem_map, peerF_sessMap]; exact hpf hjl
        obtain ⟨-, hal⟩ := ideal_alone Adv hE true qu f i1 adv1 e1' s1' r1 res (by omega)
          (by rw [hiv]; exact idealBnd_of_related hR' hb') h
        obtain ⟨hjF, hpF⟩ := hal jU.val hj1 hp1
        obtain ⟨-, -, -, -, -, hj, hne, -⟩ := hw
        exact hne hpF


/-! ## The main statements -/

/-- ~badList~ has at most ~q + 1~ entries: at most one comparison per query,
plus the final guess. -/
theorem badList_length {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (adv : A) (qu : Std.Usize) (j : Std.Usize) (t ot : GameTape Seed Coins qu.val) :
    (badList E Adv adv qu j t ot).length ≤ qu.val + 1 := by
  unfold badList
  split
  · rename_i hx
    have := (symRun_facts Adv hE qu.val 0 hx.choose (symWorld P t ot j) (alloc.vec.Vec.new _)
      Response.Rejected (by simp [SymBnd, symWorld]) (by scalar_tac)).2
    simpa [symWorld] using this
  · simp

/-- **Winning the ideal game means hitting the bad list.** If the adversary
wins the ideal secrecy game with Lowe's fix, it names some session ~j < q~,
and session ~j~'s nonce is in the bad list computed with session ~j~'s nonce
erased. -/
theorem ideal_win_bad {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct) (hE : E.Total)
    (adv : A) (qu : Std.Usize) (t ot : GameTape Seed Coins qu.val) (a' : A)
    (h : secrecy_game E (gameTape Seed Coins qu.val)
      (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins qu.val)) Adv true t
      (idealOracle P ot) adv qu = ok (true, a')) :
    ∃ j : Fin qu.val, t.nonces j ∈ badList E Adv adv qu (natU j.val) (erase j t) ot := by
  unfold secrecy_game at h
  obtain ⟨t0, ht0, h⟩ := bind_inv h
  obtain ⟨⟨pk, sk⟩, hk, h⟩ := bind_inv h
  obtain ⟨pks, hpks, h⟩ := bind_inv h
  obtain ⟨pks1, hpks1, h⟩ := bind_inv h
  obtain ⟨adv1, hadv1, h⟩ := bind_inv h
  obtain ⟨env, henv, h⟩ := bind_inv h
  obtain ⟨⟨adv2, ss, last⟩, hl, h⟩ := bind_inv h
  obtain ⟨⟨⟨k, g⟩, adv3⟩, hg, h⟩ := bind_inv h
  obtain ⟨b, hb, h⟩ := bind_inv h
  have hb' : b = true := by
    cases b
    · simp at h
    · rfl
  subst hb'
  simp only [ite_true] at h
  obtain ⟨s2, hs2, h⟩ := bind_inv h
  obtain ⟨i, hi, h⟩ := bind_inv h
  simp only [Result.ok.injEq, Prod.mk.injEq, decide_eq_true_eq] at h
  obtain ⟨hig, -⟩ := h
  have hhon := honest_spec core.marker.CopyU64 ss k
  rw [hb] at hhon
  simp only [WP.spec_ok, true_iff] at hhon
  obtain ⟨hkl, hpeer⟩ := hhon
  have hs2' : s2 = ss.val[k.val] := by
    have := alloc.vec.Vec.index_usize_spec ss k hkl
    rw [alloc.vec.Vec.index_slice_index] at hs2
    rw [hs2] at this
    simpa using this
  have hng : nonceF ss.val[k.val] = g := by
    rw [← hs2', ← hig]
    cases s2 <;> simp_all [Session.nonce, nonceF]
  have henv' : env = { tape := t, oracle := idealOracle P ot, count := 0#usize, pke := () } := by
    simp [World.new] at henv; exact henv.symm
  subst henv'
  obtain ⟨hlen, -⟩ := ideal_alone Adv hE true qu qu.val 0#usize adv1 _ (alloc.vec.Vec.new _)
    Response.Rejected _ (by simp) (by simp [IdealBnd, idealOracle]) hl
  simp only at hlen
  have hkq : k.val < qu.val := by omega
  refine ⟨⟨k.val, hkq⟩, ?_⟩
  simp only [natU_val]
  -- The same start on the erased tape.
  have hstart : gameStart E (gameTape Seed Coins qu.val)
      (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins qu.val)) Adv
      (erase ⟨k.val, hkq⟩ t) (idealOracle P ot) adv = ok adv1 := by
    have hs : (gameTape Seed Coins qu.val).seed (erase ⟨k.val, hkq⟩ t) ADVERSARY =
        (gameTape Seed Coins qu.val).seed t ADVERSARY := rfl
    unfold gameStart
    rw [hs, ht0]
    simp only [bind_ok]
    rw [hk]
    simp only [bind_ok]
    show (do
      let pks ← (alloc.vec.Vec.new Pk).push pk
      let pks1 ← secrecy_game_loop0 (IdealOracle.Insts.ExamplesNslOracle E
        (gameTape Seed Coins qu.val)) (idealOracle P ot) pks 1#usize
      Adv.start adv pks1.deref sk) = ok adv1
    rw [hpks]
    simp only [bind_ok]
    rw [hpks1]
    simp only [bind_ok]
    exact hadv1
  unfold badList
  have hx : ∃ a1, gameStart E (gameTape Seed Coins qu.val)
      (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins qu.val)) Adv
      (erase ⟨k.val, hkq⟩ t) (idealOracle P ot) adv = ok a1 := ⟨_, hstart⟩
  rw [dif_pos hx]
  have hc := hx.choose_spec
  generalize hx.choose = x at hc ⊢
  rw [hstart] at hc
  simp only [Result.ok.injEq] at hc
  subst hc
  -- The symbolic world starts related to the ideal one and satisfies the invariant.
  obtain ⟨env0, henv0, hinv0, -⟩ := secInv_new E (gameTape Seed Coins qu.val)
    (gameTape Seed Coins qu.val) (erase ⟨k.val, hkq⟩ t) ot k
  have : env0 = symWorld P (erase ⟨k.val, hkq⟩ t) ot k := by
    simp [Symbolic.new, RealOracle.new, symWorld] at henv0; exact henv0.symm
  subst this
  have hR : Related (gameTape Seed Coins qu.val) (gameTape Seed Coins qu.val) k
      (t.nonces ⟨k.val, hkq⟩)
      { tape := t, oracle := (idealOracle (Pk := Pk) (Sk := Sk) (Ct := Ct) P ot), count := 0#usize,
        pke := () } (alloc.vec.Vec.new _)
      (symWorld (Pk := Pk) (Sk := Sk) (Ct := Ct) P (erase ⟨k.val, hkq⟩ t) ot k) (alloc.vec.Vec.new _) := by
    refine ⟨fun _ => rfl, fun _ => rfl, fun k' hk' => ?_, ?_, rfl, rfl, rfl, rfl, by simp [idealOracle, symWorld], by simp⟩
    · simp only [gameTape, symWorld, erase, Result.ok.injEq]
      split
      · rename_i h'
        rw [Function.update_of_ne]
        intro heq
        apply hk'
        simp only [Fin.mk.injEq] at heq
        exact UScalar.eq_of_val_eq heq
      · rfl
    · simp [gameTape, hkq]
  exact couple Adv hE qu k (t.nonces ⟨k.val, hkq⟩) qu.val 0#usize adv1 _ (alloc.vec.Vec.new _)
    Response.Rejected (symWorld P (erase ⟨k.val, hkq⟩ t) ot k) (alloc.vec.Vec.new _) _
    (by simp) hR (by simp [SymBnd, symWorld]) hinv0 rfl (by simp [NonceInv]) hl
    ⟨k, g, adv3, hg, rfl, hkl, hpeer, hng⟩

end examples.nsl.Game
