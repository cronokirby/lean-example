module

public import Examples.Nsl.Lawful

/-! # Lowe's attack on Needham–Schroeder

`lowe_attack` runs the real secrecy game (`World` over `RealOracle`) with
`lowe = false` against the adversary `LoweAttack` and shows that it wins.

The proof evaluates the run symbolically. The functions of a total `Pke` and of
total tapes become pure functions (`keygenF`, `encF`, `decF`, `seedF`,
`coinsF`, `nonceF`, chosen by `Classical.choose`), and `Pke.Correct` gives
`decF_encF`, which closes the three decryptions the run depends on. Each of the
three rounds gets a lemma for the adversary's move (`next0_eq`, `next1_eq`,
`next2_eq`) and one for the protocol step (`step0.spec`, `step1.spec`,
`step2.spec`); `game.spec` unfolds the game loop three times and chains them.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl
namespace Attack

variable {P Seed Coins Pk Sk Ct T : Type _}

section Pke
variable {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)

noncomputable def keygenF (s : Seed) : Pk × Sk := Classical.choose (hE.keygen_ok s)
noncomputable def encF (pk : Pk) (m : Msg Std.U64) (r : Coins) : Ct :=
  Classical.choose (hE.enc_ok pk m r)
noncomputable def decF (sk : Sk) (c : Ct) : Option (Msg Std.U64) :=
  Classical.choose (hE.dec_ok sk c)

theorem keygen_eq (s : Seed) : E.keygen s = ok (keygenF hE s) :=
  Classical.choose_spec (hE.keygen_ok s)
theorem enc_eq (pk : Pk) (m : Msg Std.U64) (r : Coins) : E.enc pk m r = ok (encF hE pk m r) :=
  Classical.choose_spec (hE.enc_ok pk m r)
theorem dec_eq (sk : Sk) (c : Ct) : E.dec sk c = ok (decF hE sk c) :=
  Classical.choose_spec (hE.dec_ok sk c)

theorem keygen.spec (s : Seed) : E.keygen s ⦃ k => k = keygenF hE s ⦄ := by
  rw [Classical.choose_spec (hE.keygen_ok s)]; simp [keygenF]

theorem enc.spec (pk : Pk) (m : Msg Std.U64) (r : Coins) :
    E.enc pk m r ⦃ c => c = encF hE pk m r ⦄ := by
  rw [Classical.choose_spec (hE.enc_ok pk m r)]; simp [encF]

theorem dec.spec (sk : Sk) (c : Ct) : E.dec sk c ⦃ m => m = decF hE sk c ⦄ := by
  rw [Classical.choose_spec (hE.dec_ok sk c)]; simp [decF]

end Pke

/-- Decrypting with the matching secret key inverts encryption. -/
theorem decF_encF {E : Pke P Seed Coins Pk Sk Ct} (hT : E.Total) (hE : E.Correct) (s : Seed)
    (m : Msg Std.U64) (r : Coins) :
    decF hT (keygenF hT s).2 (encF hT (keygenF hT s).1 m r) =
      some m := by
  have hk : E.keygen s = ok (keygenF hT s) := Classical.choose_spec (hE.keygen_ok s)
  have hc : E.enc (keygenF hT s).1 m r = ok (encF hT (keygenF hT s).1 m r) :=
    Classical.choose_spec (hE.enc_ok _ m r)
  have hd : E.dec (keygenF hT s).2 (encF hT (keygenF hT s).1 m r) =
      ok (decF hT (keygenF hT s).2 (encF hT (keygenF hT s).1 m r)) :=
    Classical.choose_spec (hE.dec_ok _ _)
  have := hE.dec_enc s (keygenF hT s).1 (keygenF hT s).2 m r _ hk hc
  rw [hd] at this
  simpa using this

section Tape
variable {I : Tape T Seed Coins} (hI : I.Total)

noncomputable def seedF (t : T) (a : Std.U8) : Seed := Classical.choose (hI.seed_ok t a)
noncomputable def coinsF (t : T) (i : Std.Usize) : Coins := Classical.choose (hI.coins_ok t i)
noncomputable def nonceF (t : T) (k : Std.Usize) : Std.U64 := Classical.choose (hI.nonce_ok t k)

theorem seed_eq (t : T) (a : Std.U8) : I.seed t a = ok (seedF hI t a) :=
  Classical.choose_spec (hI.seed_ok t a)
theorem coins_eq (t : T) (i : Std.Usize) : I.coins t i = ok (coinsF hI t i) :=
  Classical.choose_spec (hI.coins_ok t i)
theorem nonce_eq (t : T) (k : Std.Usize) : I.nonce t k = ok (nonceF hI t k) :=
  Classical.choose_spec (hI.nonce_ok t k)

theorem seed.spec (t : T) (a : Std.U8) : I.seed t a ⦃ s => s = seedF hI t a ⦄ := by
  rw [Classical.choose_spec (hI.seed_ok t a)]; simp [seedF]

theorem coins.spec (t : T) (i : Std.Usize) : I.coins t i ⦃ r => r = coinsF hI t i ⦄ := by
  rw [Classical.choose_spec (hI.coins_ok t i)]; simp [coinsF]

theorem nonce.spec (t : T) (k : Std.Usize) : I.nonce t k ⦃ n => n = nonceF hI t k ⦄ := by
  rw [Classical.choose_spec (hI.nonce_ok t k)]; simp [nonceF]

end Tape

attribute [local step] keygen.spec enc.spec dec.spec seed.spec coins.spec nonce.spec

/-- The first loop of the game collects the public keys of agents
`agent..256`; we only need the length and the key of agent 2. -/
theorem loop0.spec {O : Type _} (OI : Oracle O Pk Ct) (oracle : O) (f : Std.U8 → Pk)
    (hf : ∀ a, OI.pk oracle a = ok (f a))
    (pks : alloc.vec.Vec Pk) (agent : Std.Usize) (h1 : agent.val ≤ 256)
    (h2 : pks.length = agent.val) (h3 : 2 < agent.val → pks.val[2]? = some (f 2#u8)) :
    secrecy_game_loop0 OI oracle pks agent ⦃ r =>
      r.length = 256 ∧ r.val[2]? = some (f 2#u8) ⦄ := by
  unfold secrecy_game_loop0
  simp only [hf]
  step*
  · simp only [alloc.vec.Vec.length, pks1_post, List.length_append, List.length_singleton]
    simp only [alloc.vec.Vec.length] at h2
    omega
  · intro h
    by_cases ha : agent.val = 2
    · have hi : i.val = 2 := by simp [i_post, UScalar.cast_val_eq]; scalar_tac
      have hi' : i = 2#u8 := by scalar_tac
      have hl : pks.val.length = 2 := by simp only [alloc.vec.Vec.length] at h2; omega
      rw [pks1_post, List.getElem?_append_right (by omega), hl, hi']
      simp
    · have hl : 2 < pks.val.length := by simp only [alloc.vec.Vec.length] at h2; omega
      rw [pks1_post, List.getElem?_append_left hl]
      exact h3 (by omega)
termination_by 256 - agent.val
decreasing_by scalar_decr_tac


theorem loop0_real.spec {U : Type _} {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
    {UI : Tape U Seed Coins} (hU : UI.Total) (oracle : RealOracle P U) (pks : alloc.vec.Vec Pk)
    (h : pks.length = 1) :
    secrecy_game_loop0 (RealOracle.Insts.ExamplesNslOracle E UI) oracle pks 1#usize ⦃ r =>
      r.length = 256 ∧ r.val[2]? = some (keygenF hE (seedF hU oracle.tape 2#u8)).1 ⦄ := by
  apply loop0.spec _ _ (fun a => (keygenF hE (seedF hU oracle.tape a)).1)
  · intro a
    simp [RealOracle.Insts.ExamplesNslOracle.pk, seed_eq hU, keygen_eq hE]
    rfl
  · simp
  · simpa using h
  · simp

theorem start.spec {E : Pke P Seed Coins Pk Sk Ct} (cpk : core.marker.Copy Pk)
    (csk : core.marker.Copy Sk) (self : LoweAttack P Seed Coins Pk Sk Ct) (pks : Slice Pk) (sk : Sk)
    (h : 2 < pks.length) :
    LoweAttack.Insts.ExamplesNslAdversary.start E cpk csk self pks sk ⦃ a =>
      a = { self with pk_b := pks.val[2]?, sk := some sk } ⦄ := by
  unfold LoweAttack.Insts.ExamplesNslAdversary.start
  simp [B]
  step*
  have hi : i.val = 2 := by
    simp [i_post, UScalar.cast_val_eq]; cases System.Platform.numBits_eq <;> simp [*]
  rw [List.getElem?_eq_getElem (by scalar_tac), t_post]
  simp [hi]

/-! ## The adversary's moves -/

/-- The adversary's round counter advances by one while it is below 3. -/
theorem round_succ (r s : Std.U8) (h : r.val < 3) (hs : s.val = r.val + 1) :
    (if r < 3#u8 then r + 1#u8 else ok r) = ok s := by
  have h1 : r + 1#u8 ⦃ z => z = s ⦄ := by
    step as ⟨z, hz⟩
    exact UScalar.eq_of_val_eq (by scalar_tac)
  split
  · cases hm : r + 1#u8 <;> simp_all
  · scalar_tac

section Adv
variable {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total) (cpk : core.marker.Copy Pk)
  (csk : core.marker.Copy Sk)

theorem next0_eq (self : LoweAttack P Seed Coins Pk Sk Ct) (last : Response Ct)
    (h : self.round = 0#u8) :
    LoweAttack.Insts.ExamplesNslAdversary.next E cpk csk self last =
      ok (Action.Start A ADVERSARY, { self with round := 1#u8 }) := by
  have hs := round_succ 0#u8 1#u8 (by scalar_tac) (by scalar_tac)
  unfold LoweAttack.Insts.ExamplesNslAdversary.next
  rw [h, hs]
  simp only [bind_ok]
  rfl

include hE in
theorem next1_eq (self : LoweAttack P Seed Coins Pk Sk Ct) (ct : Ct) (pkb : Pk) (sk : Sk)
    (na : Std.U64) (x : Std.U8)
    (h : self.round = 1#u8) (hpk : self.pk_b = some pkb) (hsk : self.sk = some sk)
    (hd : decF hE sk ct = some (Msg.One na x)) :
    LoweAttack.Insts.ExamplesNslAdversary.next E cpk csk self (Response.Sent ct) =
      ok (Action.Respond B (encF hE pkb (Msg.One na A) self.coins),
        { self with round := 2#u8 }) := by
  have hs := round_succ 1#u8 2#u8 (by scalar_tac) (by scalar_tac)
  unfold LoweAttack.Insts.ExamplesNslAdversary.next
  rw [h, hs]
  simp only [LoweAttack.decrypt, hsk, hpk, dec_eq hE, hd, enc_eq hE, bind_ok]
  rfl

theorem next2_eq (self : LoweAttack P Seed Coins Pk Sk Ct) (ct : Ct)
    (h : self.round = 2#u8) :
    LoweAttack.Insts.ExamplesNslAdversary.next E cpk csk self (Response.Sent ct) =
      ok (Action.Deliver 0#usize ct, { self with round := 3#u8 }) := by
  have hs := round_succ 2#u8 3#u8 (by scalar_tac) (by scalar_tac)
  unfold LoweAttack.Insts.ExamplesNslAdversary.next
  rw [h, hs]
  simp only [bind_ok]
  rfl

include hE in
theorem guess.spec (self : LoweAttack P Seed Coins Pk Sk Ct) (ct : Ct) (sk : Sk) (nb : Std.U64)
    (hsk : self.sk = some sk) (hd : decF hE sk ct = some (Msg.Three nb)) :
    LoweAttack.Insts.ExamplesNslAdversary.guess E cpk csk self (Response.Sent ct) ⦃ kg _ =>
      kg = (1#usize, nb) ⦄ := by
  unfold LoweAttack.Insts.ExamplesNslAdversary.guess
  simp [LoweAttack.decrypt, hsk, dec_eq hE, hd]

end Adv

/-! ## The protocol steps of the run -/

section Steps
variable {U : Type _} {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins} (hT : TI.Total) (hU : UI.Total)

include hE hT in
/-- Round 0: A starts a session with the adversary and sends it message one. -/
theorem step0.spec (env : World P T (RealOracle P U)) (hc : env.count.val < 10) :
    nsl.step
      (World.Insts.ExamplesNslEnvClause0_CtU64 E TI (RealOracle.Insts.ExamplesNslOracle E UI))
      false env (alloc.vec.Vec.new _) (Action.Start A ADVERSARY) ⦃ resp env' ss =>
      resp = Response.Sent (encF hE (keygenF hE (seedF hT env.tape ADVERSARY)).1
        (Msg.One (nonceF hT env.tape 0#usize) A) (coinsF hT env.tape env.count)) ∧
      env'.tape = env.tape ∧ env'.oracle = env.oracle ∧ env'.count.val = env.count.val + 1 ∧
      ss.val = [Session.Initiating A ADVERSARY (nonceF hT env.tape 0#usize)] ⦄ := by
  unfold nsl.step
  simp only [World.Insts.ExamplesNslEnvClause0_CtU64.nonce,
    World.Insts.ExamplesNslEnvClause0_CtU64.enc]
  simp [A, ADVERSARY]
  step*
  obtain ⟨pk, sk⟩ := x
  step*
  simp only [Prod.ext_iff] at *
  simp_all
  exact ⟨rfl, rfl⟩

include hE hT hU in
/-- Round 1: B receives the adversary's re-encryption of message one, starts a
responder session believing it talks to A, and sends message two to A. -/
theorem step1.spec (env : World P T (RealOracle P U)) (sessions : alloc.vec.Vec (Session Std.U64))
    (hs : sessions.length = 1) (ct : Ct) (na : Std.U64)
    (hd : decF hE (keygenF hE (seedF hU env.oracle.tape B)).2 ct = some (Msg.One na A))
    (hc : env.oracle.count.val < 10) :
    nsl.step
      (World.Insts.ExamplesNslEnvClause0_CtU64 E TI (RealOracle.Insts.ExamplesNslOracle E UI))
      false env sessions (Action.Respond B ct) ⦃ resp env' ss =>
      resp = Response.Sent (encF hE (keygenF hE (seedF hU env.oracle.tape A)).1
        (Msg.Two na (nonceF hT env.tape 1#usize) B)
        (coinsF hU env.oracle.tape env.oracle.count)) ∧
      env'.tape = env.tape ∧ env'.count = env.count ∧ env'.oracle.tape = env.oracle.tape ∧
      ss.val = sessions.val ++ [Session.Responding B A na (nonceF hT env.tape 1#usize)] ⦄ := by
  have hlen : alloc.vec.Vec.len sessions = 1#usize := by
    apply UScalar.eq_of_val_eq; simp only [alloc.vec.Vec.len_val]; scalar_tac
  unfold nsl.step
  rw [hlen]
  simp only [World.Insts.ExamplesNslEnvClause0_CtU64.nonce,
    World.Insts.ExamplesNslEnvClause0_CtU64.enc,
    World.Insts.ExamplesNslEnvClause0_CtU64.dec, RealOracle.Insts.ExamplesNslOracle.dec,
    RealOracle.Insts.ExamplesNslOracle.enc, RealOracle.Insts.ExamplesNslOracle.pk]
  simp [A, B, ADVERSARY, seed_eq hU, keygen_eq hE, dec_eq hE]
  simp [A, B] at hd
  generalize keygenF hE (seedF hU env.oracle.tape 2#u8) = kB at hd ⊢
  obtain ⟨pkB, skB⟩ := kB
  simp at hd ⊢
  simp [hd]
  step*
  generalize keygenF hE (seedF hU env.oracle.tape 1#u8) = kA
  obtain ⟨pkA, skA⟩ := kA
  simp only
  step*
  simp_all

include hE hT hU in
/-- Round 2: A's session 0 receives B's message two. Without Lowe's check A does
not notice that B is not its peer, accepts, and sends B's nonce to the
adversary in message three. -/
theorem step2.spec (env : World P T (RealOracle P U)) (sessions : alloc.vec.Vec (Session Std.U64))
    (n_a n_b : Std.U64) (r : Std.U8) (s1 : Session Std.U64)
    (hs : sessions.val = [Session.Initiating A ADVERSARY n_a, s1]) (ct : Ct)
    (hd : decF hE (keygenF hE (seedF hU env.oracle.tape A)).2 ct = some (Msg.Two n_a n_b r))
    (hc : env.count.val < 10) :
    nsl.step
      (World.Insts.ExamplesNslEnvClause0_CtU64 E TI (RealOracle.Insts.ExamplesNslOracle E UI))
      false env sessions (Action.Deliver 0#usize ct) ⦃ resp _ ss =>
      resp = Response.Sent (encF hE (keygenF hE (seedF hT env.tape ADVERSARY)).1
        (Msg.Three n_b) (coinsF hT env.tape env.count)) ∧
      ss.val = [Session.Initiated A ADVERSARY n_a n_b, s1] ⦄ := by
  unfold nsl.step
  simp only [World.Insts.ExamplesNslEnvClause0_CtU64.enc,
    World.Insts.ExamplesNslEnvClause0_CtU64.same,
    World.Insts.ExamplesNslEnvClause0_CtU64.dec, RealOracle.Insts.ExamplesNslOracle.dec]
  simp [A, ADVERSARY, seed_eq hU, keygen_eq hE, dec_eq hE]
  simp [A, ADVERSARY] at hd hs
  step*
  rename_i hsplit
  have hinit : Session.Initiating owner peer na = Session.Initiating 1#u8 0#u8 n_a := by
    rw [← hsplit, s_post]; simp [hs]
  simp only [Session.Initiating.injEq] at hinit
  obtain ⟨rfl, rfl, rfl⟩ := hinit
  generalize keygenF hE (seedF hU env.oracle.tape 1#u8) = kA at hd ⊢
  obtain ⟨pkA, skA⟩ := kA
  simp only at hd ⊢
  simp [hd]
  step*
  subst x_post
  generalize keygenF hE (seedF hT env.tape 0#u8) = k0
  obtain ⟨pk0, sk0⟩ := k0
  simp only
  step*
  simp_all [alloc.vec.Vec.set_val_eq]

end Steps

section Game
variable {U : Type _} {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Correct)
  (cpk : core.marker.Copy Pk) (csk : core.marker.Copy Sk)
  {TI : Tape T Seed Coins} {UI : Tape U Seed Coins} (hT : TI.Total) (hU : UI.Total)

include hE hT hU in
theorem game.spec (tape : T) (oracle_tape : U) (coins : Coins) :
    secrecy_game E TI (RealOracle.Insts.ExamplesNslOracle E UI)
      (LoweAttack.Insts.ExamplesNslAdversary E cpk csk) false tape
      ⟨oracle_tape, 0#usize, ()⟩ ⟨coins, none, none, 0#u8⟩ 3#usize ⦃ b _ =>
      b = true ⦄ := by
  have hE' := hE.toTotal
  unfold secrecy_game
  step*
  step with loop0_real.spec hE' hU
  step with start.spec
  · simp only [alloc.vec.Vec.length] at pks1_post
    simp [alloc.vec.Vec.deref, Slice.length, pks1_post]
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp pk_post
  subst t_post adversary1_post
  simp only [World.new, bind_ok]
  -- Round 0.
  rw [secrecy_game_loop1]
  simp only [show (0#usize : Std.Usize) < 3#usize by scalar_tac, ↓reduceIte]
  simp only [LoweAttack.Insts.ExamplesNslAdversary]
  rw [next0_eq _ _ _ _ rfl]
  simp only [bind_ok]
  step with step0.spec hE' hT as ⟨res1, hl1, hte1, hor1, hc1, hss1⟩
  obtain ⟨last1, env1, ss1⟩ := res1
  simp only at hl1 hte1 hor1 hc1 hss1 ⊢
  step as ⟨i1, hi1⟩
  -- Round 1.
  rw [secrecy_game_loop1]
  simp only [show i1 < 3#usize by scalar_tac, ↓reduceIte]
  rw [hl1, next1_eq hE' cpk csk _ _ (keygenF hE' (seedF hU oracle_tape 2#u8)).1
    (keygenF hE' (seedF hT tape ADVERSARY)).2 (nonceF hT tape 0#usize) A rfl ?hpk rfl ?hd]
  case hpk => simpa [alloc.vec.Vec.deref] using pks1_post1
  case hd => exact decF_encF hE' hE _ _ _
  simp only [bind_ok]
  have hs1 : ss1.length = 1 := by simp [alloc.vec.Vec.length, hss1]
  have hd1 : decF hE' (keygenF hE' (seedF hU env1.oracle.tape B)).2
      (encF hE' (keygenF hE' (seedF hU oracle_tape 2#u8)).1
        (Msg.One (nonceF hT tape 0#usize) A) coins) =
      some (Msg.One (nonceF hT tape 0#usize) A) := by
    rw [hor1]; simp only [B]; exact decF_encF hE' hE _ _ _
  have hc1' : env1.oracle.count.val < 10 := by simp [hor1]
  step with step1.spec hE' hT hU env1 ss1 hs1 _ _ hd1 hc1' as ⟨res2, hl2, hte2, hc2, hot2, hss2⟩
  obtain ⟨last2, env2, ss2⟩ := res2
  simp only at hl2 hte2 hc2 hot2 hss2 ⊢
  step as ⟨i2, hi2⟩
  -- Round 2.
  rw [secrecy_game_loop1]
  simp only [show i2 < 3#usize by scalar_tac, ↓reduceIte]
  rw [hl2, next2_eq cpk csk _ _ rfl]
  simp only [bind_ok]
  have hs2 : ss2.val = [Session.Initiating A ADVERSARY (nonceF hT tape 0#usize),
      Session.Responding B A (nonceF hT tape 0#usize) (nonceF hT env1.tape 1#usize)] := by
    simp [hss2, hss1]
  have hd2 : decF hE' (keygenF hE' (seedF hU env2.oracle.tape A)).2
      (encF hE' (keygenF hE' (seedF hU env1.oracle.tape A)).1
        (Msg.Two (nonceF hT tape 0#usize) (nonceF hT env1.tape 1#usize) B)
        (coinsF hU env1.oracle.tape env1.oracle.count)) =
      some (Msg.Two (nonceF hT tape 0#usize) (nonceF hT env1.tape 1#usize) B) := by
    rw [hot2]; exact decF_encF hE' hE _ _ _
  have hc2' : env2.count.val < 10 := by rw [hc2]; omega
  step with step2.spec hE' hT hU env2 ss2 _ _ _ _ hs2 _ hd2 hc2' as ⟨res3, hl3, hss3⟩
  obtain ⟨last3, env3, ss3⟩ := res3
  simp only at hl3 hss3 ⊢
  step as ⟨i3, hi3⟩
  -- The loop ends after three queries.
  rw [secrecy_game_loop1]
  simp only [show ¬ i3 < 3#usize by scalar_tac, ↓reduceIte, bind_ok]
  -- The guess: the adversary decrypts message three and names B's session.
  have hd3 : decF hE' (keygenF hE' (seedF hT tape ADVERSARY)).2
      (encF hE' (keygenF hE' (seedF hT env2.tape ADVERSARY)).1
        (Msg.Three (nonceF hT env1.tape 1#usize)) (coinsF hT env2.tape env2.count)) =
      some (Msg.Three (nonceF hT env1.tape 1#usize)) := by
    rw [hte2, hte1]; exact decF_encF hE' hE _ _ _
  rw [hl3]
  step with guess.spec hE' cpk csk
    ⟨coins, _, some (keygenF hE' (seedF hT tape ADVERSARY)).2, 3#u8⟩ _ _ _ rfl hd3
  simp only [honest]
  subst_vars
  have hl : ss3.val.length = 2 := by simp [hss3]
  have hlen : (1#usize : Std.Usize) < ss3.deref.len := by
    have : (ss3.deref.len).val = 2 := by
      simp [alloc.vec.Vec.deref, hl]
    scalar_tac
  simp only [hlen, ↓reduceIte]
  step*
  simp [x_post, alloc.vec.Vec.deref, hss3, Session.peer, Session.nonce, A, B, ADVERSARY,
    alloc.vec.Vec.index_usize]
end Game

/-- A run whose result satisfies the spec "the boolean is `true`" returns
`ok (true, _)`. -/
theorem exists_of_spec {α : Type _} {m : Result (Bool × α)} (h : m ⦃ b _ => b = true ⦄) :
    ∃ a, m = ok (true, a) := by
  cases m with
  | ret x =>
    obtain ⟨b, a⟩ := x
    simp at h
    exact ⟨a, by rw [h]⟩
  | vis e k => simp at h
  | div => simp at h

end Attack

public section

/-- **Lowe's attack on Needham–Schroeder.**

Without Lowe's check (`lowe = false`) the adversary `LoweAttack` wins the real
secrecy game with three queries: the game returns `ok (true, _)`. It holds for
every correct public-key encryption scheme `E` (`E.Correct`: total, and
decryption with the matching secret key inverts encryption), every total pair of
tapes, and all randomness (`tape`, `oracle_tape`, the adversary's `coins`).
So the attack succeeds with probability 1, whatever the encryption.

The run: honest A (agent 1) starts a session with the adversary (agent 0). The
adversary decrypts A's message one `{Na, A}` and re-encrypts it to honest B
(agent 2). B starts responder session 1 with peer A and replies `{Na, Nb, B}`
encrypted to A. The adversary forwards it to A's session 0, which accepts it
because it does not check that the responder is its peer, and sends `{Nb}` to
the adversary. The adversary decrypts it and names session 1, whose peer A is
honest and whose nonce is `Nb`.

`cpk` and `csk` are the `Copy` instances the Rust adversary requires on keys;
the extracted code never uses them. -/
theorem lowe_attack {P Seed Coins Pk Sk Ct T U : Type _} {E : Pke P Seed Coins Pk Sk Ct}
    (hE : E.Correct) (cpk : core.marker.Copy Pk) (csk : core.marker.Copy Sk)
    {TI : Tape T Seed Coins} {UI : Tape U Seed Coins} (hT : TI.Total) (hU : UI.Total)
    (tape : T) (oracle_tape : U) (coins : Coins) :
    ∃ adv, (do
      let o ← RealOracle.new E UI oracle_tape
      let a ← LoweAttack.new E coins
      secrecy_game E TI (RealOracle.Insts.ExamplesNslOracle E UI)
        (LoweAttack.Insts.ExamplesNslAdversary E cpk csk) false tape o a 3#usize) =
      ok (true, adv) := by
  simp only [RealOracle.new, LoweAttack.new, bind_ok]
  exact Attack.exists_of_spec (Attack.game.spec hE cpk csk hT hU tape oracle_tape coins)

end

end examples.nsl
