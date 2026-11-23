module

public import Examples.Gen.Funs

/-! # Pure models of the NSL environments

The extracted `nsl.step` is generic over an `Env`. Here it is modelled once,
as `pstep`, over a pure environment `PEnv` (state-passing functions without
`Result`). The ideal world (`World` over `IdealOracle`) and the symbolic world
(`Symbolic`) are modelled as `idealEnv` and `symEnv` on abstract states that
keep only the counters and tables, with the tapes and the `Pke` as pure
functions. `Examples.Nsl.Faithful.Spec` shows that the extracted code computes
these models; this file proves the facts about them that faithfulness needs.
-/

@[expose] public noncomputable section

open Aeneas Aeneas.Std Result

namespace examples.nsl.Model

open Classical

set_option linter.unusedSimpArgs false

/-- A `Usize` from a natural number (wrapping; exact below `2 ^ numBits`). -/
def natU (i : Nat) : Std.Usize := ⟨BitVec.ofNat _ i⟩

theorem natU_val (x : Std.Usize) : natU x.val = x := by
  cases x; simp [natU, UScalar.val]

/-- A tape as pure functions. Coins are indexed by a counter. -/
structure TapeF (Seed Coins : Type _) where
  seed : Std.U8 → Seed
  coins : Nat → Coins
  nonce : Std.Usize → Std.U64

/-- A `Pke` as pure functions. -/
structure PkeF (Seed Coins Pk Sk Ct : Type _) where
  keygen : Seed → Pk × Sk
  enc : Pk → Msg Std.U64 → Coins → Ct
  dec : Sk → Ct → Option (Msg Std.U64)

/-! ## Messages, sessions, table entries -/

def msgMap {N M : Type _} (f : N → M) : Msg N → Msg M
  | .One a x => .One (f a) x
  | .Two a b x => .Two (f a) (f b) x
  | .Three a => .Three (f a)

def sessMap {N M : Type _} (f : N → M) : Session N → Session M
  | .Initiating o p a => .Initiating o p (f a)
  | .Initiated o p a b => .Initiated o p (f a) (f b)
  | .Responding o p a b => .Responding o p (f a) (f b)
  | .Responded o p a b => .Responded o p (f a) (f b)

/-- The peer of a session. -/
def peerF {N : Type _} : Session N → Std.U8
  | .Initiating _ p _ => p
  | .Initiated _ p _ _ => p
  | .Responding _ p _ _ => p
  | .Responded _ p _ _ => p

/-- The nonce a session generated. -/
def nonceF {N : Type _} : Session N → N
  | .Initiating _ _ a => a
  | .Initiated _ _ a _ => a
  | .Responding _ _ _ b => b
  | .Responded _ _ _ b => b

@[simp, grind =] theorem peerF_sessMap {N M : Type _} (f : N → M) (s : Session N) :
    peerF (sessMap f s) = peerF s := by cases s <;> rfl

@[simp, grind =] theorem nonceF_sessMap {N M : Type _} (f : N → M) (s : Session N) :
    nonceF (sessMap f s) = f (nonceF s) := by cases s <;> rfl

def entryMap {C N M : Type _} (f : N → M) (e : Entry C N) : Entry C M :=
  { «to» := e.«to», ct := e.ct, msg := msgMap f e.msg }

/-- `lookup` on a list. -/
def lookupF {C N : Type _} : List (Entry C N) → Std.U8 → C → Option (Msg N)
  | [], _, _ => none
  | e :: es, b, c => if e.«to» = b ∧ e.ct = c then some e.msg else lookupF es b c

theorem lookupF_map {C N M : Type _} (f : N → M) (l : List (Entry C N)) (b : Std.U8) (c : C) :
    lookupF (l.map (entryMap f)) b c = (lookupF l b c).map (msgMap f) := by
  induction l with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons, lookupF, entryMap]; split <;> simp_all

/-- What a symbolic nonce stands for when the secret is `n`. -/
def subst (n : Std.U64) : Sym → Std.U64
  | .Val v => v
  | .Secret => n

/-- `concretize`. -/
def concF : Msg Sym → Option (Msg Std.U64)
  | .One (.Val a) x => some (.One a x)
  | .Two (.Val a) (.Val b) x => some (.Two a b x)
  | .Three (.Val a) => some (.Three a)
  | _ => none

theorem concF_some {m : Msg Sym} {m' : Msg Std.U64} (h : concF m = some m') (n : Std.U64) :
    m' = msgMap (subst n) m := by
  unfold concF at h; split at h <;> simp_all [msgMap, subst]

@[simp] theorem msgMap_subst_val (n : Std.U64) (m : Msg Std.U64) :
    msgMap (subst n) (msgMap Sym.Val m) = m := by
  cases m <;> rfl

/-! ## Pure environments and the pure step -/

/-- An `Env` as pure state-passing functions. -/
structure PEnv (S N Ct : Type _) where
  nonce : S → Std.Usize → N × S
  same : S → N → N → Bool × S
  enc : S → Std.U8 → Msg N → Ct × S
  dec : S → Std.U8 → Ct → Option (Msg N) × S

/-- `nsl.step` over a pure environment. -/
def pstep {S N Ct : Type _} (pe : PEnv S N Ct) (lowe : Bool) (st : S) (ss : List (Session N)) :
    Action Ct → Response Ct × S × List (Session N)
  | .Start owner peer =>
    if owner = ADVERSARY then (.Rejected, st, ss) else
      match pe.nonce st (natU ss.length) with
      | (na, st1) =>
        match pe.enc st1 peer (.One na owner) with
        | (c, st2) => (.Sent c, st2, ss ++ [.Initiating owner peer na])
  | .Respond owner msg =>
    if owner = ADVERSARY then (.Rejected, st, ss) else
      match pe.dec st owner msg with
      | (some (.One na peer), st1) =>
        match pe.nonce st1 (natU ss.length) with
        | (nb, st2) =>
          match pe.enc st2 peer (.Two na nb owner) with
          | (c, st3) => (.Sent c, st3, ss ++ [.Responding owner peer na nb])
      | (_, st1) => (.Rejected, st1, ss)
  | .Deliver k msg =>
    if h : k.val < ss.length then
      match ss[k.val] with
      | .Initiating owner peer na =>
        match pe.dec st owner msg with
        | (some (.Two na2 nb resp), st1) =>
          match pe.same st1 na2 na with
          | (b, st2) =>
            if b = true ∧ (lowe = false ∨ resp = peer) then
              match pe.enc st2 peer (.Three nb) with
              | (c, st3) => (.Sent c, st3, ss.set k.val (.Initiated owner peer na nb))
            else (.Rejected, st2, ss)
        | (_, st1) => (.Rejected, st1, ss)
      | .Responding owner peer na nb =>
        match pe.dec st owner msg with
        | (some (.Three nb2), st1) =>
          match pe.same st1 nb2 nb with
          | (b, st2) =>
            if b = true then (.Accepted, st2, ss.set k.val (.Responded owner peer na nb))
            else (.Rejected, st2, ss)
        | (_, st1) => (.Rejected, st1, ss)
      | _ => (.Rejected, st, ss)
    else (.Rejected, st, ss)

/-- `pstep` creates at most one session and never changes a session's peer. -/
theorem pstep_sessions {S N Ct : Type _} (pe : PEnv S N Ct) (lowe : Bool) (st : S)
    (ss : List (Session N)) (a : Action Ct) (r : Response Ct) (st' : S) (ss' : List (Session N))
    (h : pstep pe lowe st ss a = (r, st', ss')) :
    ss.length ≤ ss'.length ∧ ss'.length ≤ ss.length + 1 ∧
      ∀ k (h : k < ss.length), ∃ h' : k < ss'.length, peerF ss'[k] = peerF ss[k] := by
  cases a <;> simp only [pstep] at h <;> (repeat' split at h) <;> simp at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> simp_all [List.getElem_append_left, List.getElem_set] <;>
    grind [peerF]

/-! ## The ideal world -/

/-- The state of `World` over `IdealOracle`, without the tapes: the
adversary-encryption counter, the oracle's counter and its table. -/
structure IdA (Ct : Type _) where
  count : Nat
  ocount : Nat
  table : List (Entry Ct Std.U64)

/-- `World` over `IdealOracle`, with tape `t` and oracle tape `u`. -/
def idealEnv {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t u : TapeF Seed Coins) : PEnv (IdA Ct) Std.U64 Ct where
  nonce st k := (t.nonce k, st)
  same st a b := (decide (a = b), st)
  enc st dst m :=
    if dst = ADVERSARY then
      (F.enc (F.keygen (t.seed ADVERSARY)).1 m (t.coins st.count), { st with count := st.count + 1 })
    else
      (F.enc (F.keygen (u.seed dst)).1 BLANK (u.coins st.ocount),
        { st with ocount := st.ocount + 1,
                  table := st.table ++ [{ «to» := dst, ct := F.enc (F.keygen (u.seed dst)).1 BLANK (u.coins st.ocount), msg := m }] })
  dec st b c :=
    match lookupF st.table b c with
    | some m => (some m, st)
    | none => (F.dec (F.keygen (u.seed b)).2 c, st)

/-! ## The symbolic world -/

/-- The state of `Symbolic` without the tapes and the secret's index. -/
structure SyA (Ct : Type _) where
  count : Nat
  ocount : Nat
  table : List (Entry Ct Sym)
  guesses : List Std.U64
  leaked : Bool

/-- `Symbolic` with tape `t`, oracle tape `u` and secret session `j`. -/
def symEnv {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t u : TapeF Seed Coins) (j : Std.Usize) : PEnv (SyA Ct) Sym Ct where
  nonce st k := (if k = j then .Secret else .Val (t.nonce k), st)
  same st a b :=
    match a, b with
    | .Val x, .Val y => (decide (x = y), st)
    | .Val x, .Secret => (false, { st with guesses := st.guesses ++ [x] })
    | .Secret, .Val x => (false, { st with guesses := st.guesses ++ [x] })
    | .Secret, .Secret => (true, st)
  enc st dst m :=
    if dst = ADVERSARY then
      match concF m with
      | some m' =>
        (F.enc (F.keygen (t.seed ADVERSARY)).1 m' (t.coins st.count),
          { st with count := st.count + 1 })
      | none =>
        (F.enc (F.keygen (t.seed ADVERSARY)).1 BLANK (t.coins st.count),
          { st with count := st.count + 1, leaked := true })
    else
      (F.enc (F.keygen (u.seed dst)).1 BLANK (u.coins st.ocount),
        { st with ocount := st.ocount + 1,
                  table := st.table ++ [{ «to» := dst, ct := F.enc (F.keygen (u.seed dst)).1 BLANK (u.coins st.ocount), msg := m }] })
  dec st b c :=
    match lookupF st.table b c with
    | some m => (some m, st)
    | none => ((F.dec (F.keygen (u.seed b)).2 c).map (msgMap Sym.Val), st)

/-- The ideal state is the symbolic one with the secret replaced by `n`. -/
def RelA {Ct : Type _} (n : Std.U64) (a : IdA Ct) (b : SyA Ct) : Prop :=
  a.count = b.count ∧ a.ocount = b.ocount ∧ a.table = b.table.map (entryMap (subst n))

/-- Two tapes that agree except that the first has nonce `n` at session `j`. -/
def TapeRel {Seed Coins : Type _} (j : Std.Usize) (n : Std.U64) (t1 t2 : TapeF Seed Coins) : Prop :=
  t1.seed = t2.seed ∧ t1.coins = t2.coins ∧ (∀ k, k ≠ j → t1.nonce k = t2.nonce k) ∧ t1.nonce j = n

set_option hygiene false in
macro "fin_rel" : tactic => `(tactic| (
  obtain ⟨rfl, rfl, rfl⟩ := h1; obtain ⟨rfl, rfl, rfl⟩ := h2
  simp_all [RelA, sessMap, subst, entryMap, msgMap, concF]))

set_option maxHeartbeats 4000000 in
/-- One step keeps the ideal and symbolic worlds related, as long as the symbolic
world did not compare the secret with `n`; it gives the same response unless it
also leaked. -/
theorem rel_step {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t1 t2 u : TapeF Seed Coins) (j : Std.Usize) (n : Std.U64) (ht : TapeRel j n t1 t2)
    (lowe : Bool) (a : IdA Ct) (b : SyA Ct) (s2 : List (Session Sym)) (act : Action Ct)
    (hR : RelA n a b)
    (r1 : Response Ct) (a' : IdA Ct) (s1' : List (Session Std.U64))
    (h1 : pstep (idealEnv F t1 u) lowe a (s2.map (sessMap (subst n))) act = (r1, a', s1'))
    (r2 : Response Ct) (b' : SyA Ct) (s2' : List (Session Sym))
    (h2 : pstep (symEnv F t2 u j) lowe b s2 act = (r2, b', s2'))
    (hn : n ∉ b'.guesses) :
    RelA n a' b' ∧ s1' = s2'.map (sessMap (subst n)) ∧ (b'.leaked = false → r1 = r2) := by
  obtain ⟨hseed, hcoins, hnon, hj⟩ := ht
  obtain ⟨hc, hoc, htab⟩ := hR
  cases act with
  | Start o p =>
    simp only [pstep, idealEnv, symEnv, List.length_map] at h1 h2
    by_cases ho : o = ADVERSARY <;> by_cases hk : natU s2.length = j <;>
      by_cases hp : p = ADVERSARY <;>
      simp [ho, hk, hp, hj, hnon, hseed, hcoins, hc, hoc] at h1 h2 <;> fin_rel
  | Respond o m =>
    simp only [pstep, idealEnv, symEnv, List.length_map, htab, lookupF_map] at h1 h2
    by_cases ho : o = ADVERSARY
    · simp [ho] at h1 h2; fin_rel
    simp only [ho, ite_false] at h1 h2
    rcases hl : lookupF b.table o m with _ | msg
    · rcases hd : F.dec (F.keygen (u.seed o)).2 m with _ | msg
      · simp [hl, hd] at h1 h2; fin_rel
      · cases msg with
        | One na peer =>
          by_cases hk : natU s2.length = j <;> by_cases hp : peer = ADVERSARY <;>
            simp [hl, hd, msgMap, hk, hp, hj, hnon, hseed, hcoins, hc, hoc] at h1 h2 <;> fin_rel
        | Two => simp [hl, hd, msgMap] at h1 h2; fin_rel
        | Three => simp [hl, hd, msgMap] at h1 h2; fin_rel
    · cases msg with
      | One na peer =>
        cases na <;> by_cases hk : natU s2.length = j <;> by_cases hp : peer = ADVERSARY <;>
          simp [hl, msgMap, hk, hp, hj, hnon, hseed, hcoins, hc, hoc] at h1 h2 <;> fin_rel
      | Two => simp [hl, msgMap] at h1 h2; fin_rel
      | Three => simp [hl, msgMap] at h1 h2; fin_rel
  | Deliver k m =>
    simp only [pstep, idealEnv, symEnv, List.length_map, htab, lookupF_map] at h1 h2
    by_cases hk : k.val < s2.length
    swap
    · simp [hk] at h1 h2; fin_rel
    simp only [hk, _root_.dite_true, List.getElem_map] at h1 h2
    obtain ⟨sk, hs⟩ : ∃ sk, s2[k.val] = sk := ⟨_, rfl⟩
    simp only [hs] at h1 h2
    cases sk with
    | Initiating ow pe na =>
      rcases hl : lookupF b.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd, sessMap] at h1 h2; fin_rel
        · cases msg with
          | Two na2 nb resp =>
            cases na <;> by_cases hp : pe = ADVERSARY <;>
              simp [hl, hd, sessMap, msgMap, subst, hp, hseed, hcoins, hc, hoc] at h1 h2 <;>
              (try split_ifs at h1 h2) <;> fin_rel
          | One => simp [hl, hd, sessMap, msgMap] at h1 h2; fin_rel
          | Three => simp [hl, hd, sessMap, msgMap] at h1 h2; fin_rel
      · cases msg with
        | Two na2 nb resp =>
          cases na <;> cases na2 <;> cases nb <;> by_cases hp : pe = ADVERSARY <;>
            simp [hl, sessMap, msgMap, subst, hp, hseed, hcoins, hc, hoc] at h1 h2 <;>
            (try split_ifs at h1 h2) <;> fin_rel
        | One => simp [hl, sessMap, msgMap] at h1 h2; fin_rel
        | Three => simp [hl, sessMap, msgMap] at h1 h2; fin_rel
    | Responding ow pe na nb =>
      rcases hl : lookupF b.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd, sessMap] at h1 h2; fin_rel
        · cases msg with
          | Three nb2 =>
            cases nb <;>
              simp [hl, hd, sessMap, msgMap, subst, hseed, hcoins, hc, hoc] at h1 h2 <;>
              (try split_ifs at h1 h2) <;> fin_rel
          | One => simp [hl, hd, sessMap, msgMap] at h1 h2; fin_rel
          | Two => simp [hl, hd, sessMap, msgMap] at h1 h2; fin_rel
      · cases msg with
        | Three nb2 =>
          cases nb <;> cases nb2 <;>
            simp [hl, sessMap, msgMap, subst, hseed, hcoins, hc, hoc] at h1 h2 <;>
            (try split_ifs at h1 h2) <;> fin_rel
        | One => simp [hl, sessMap, msgMap] at h1 h2; fin_rel
        | Two => simp [hl, sessMap, msgMap] at h1 h2; fin_rel
    | Initiated => simp [sessMap] at h1 h2; fin_rel
    | Responded => simp [sessMap] at h1 h2; fin_rel


set_option hygiene false in
macro "fin1" : tactic => `(tactic| (
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp_all [concF, List.prefix_append]
  done))

set_option maxHeartbeats 1000000 in
/-- The symbolic step records at most one guess, keeps `leaked` set, and
increments each counter at most once. -/
theorem symStep_facts {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t u : TapeF Seed Coins) (j : Std.Usize) (lowe : Bool) (b : SyA Ct) (s : List (Session Sym))
    (act : Action Ct) (r : Response Ct) (b' : SyA Ct) (s' : List (Session Sym))
    (h : pstep (symEnv F t u j) lowe b s act = (r, b', s')) :
    b.guesses <+: b'.guesses ∧ b'.guesses.length ≤ b.guesses.length + 1 ∧
      (b.leaked = true → b'.leaked = true) ∧
      b'.count ≤ b.count + 1 ∧ b'.ocount ≤ b.ocount + 1 ∧
      b'.table.length ≤ b.table.length + 1 := by
  cases act with
  | Start o p =>
    simp only [pstep, symEnv] at h
    by_cases ho : o = ADVERSARY <;> by_cases hk : natU s.length = j <;>
      by_cases hp : p = ADVERSARY <;> simp [ho, hk, hp] at h <;> fin1
  | Respond o m =>
    simp only [pstep, symEnv] at h
    by_cases ho : o = ADVERSARY
    · simp [ho] at h; fin1
    simp only [ho, ite_false] at h
    rcases hl : lookupF b.table o m with _ | msg
    · rcases hd : F.dec (F.keygen (u.seed o)).2 m with _ | msg
      · simp [hl, hd] at h; fin1
      · cases msg <;> try (simp [hl, hd, msgMap] at h; fin1)
        rename_i peer
        by_cases hk : natU s.length = j <;> by_cases hp : peer = ADVERSARY <;>
          simp [hl, hd, msgMap, hk, hp] at h <;> fin1
    · cases msg <;> try (simp [hl] at h; fin1)
      rename_i na peer
      cases na <;> by_cases hk : natU s.length = j <;> by_cases hp : peer = ADVERSARY <;>
        simp [hl, hk, hp] at h <;> fin1
  | Deliver k m =>
    simp only [pstep, symEnv] at h
    by_cases hk : k.val < s.length
    swap
    · simp [hk] at h; fin1
    simp only [hk, _root_.dite_true] at h
    obtain ⟨sk, hs⟩ : ∃ sk, s[k.val] = sk := ⟨_, rfl⟩
    simp only [hs] at h
    cases sk with
    | Initiating ow pe na =>
      rcases hl : lookupF b.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd] at h; fin1
        · cases msg <;> try (simp [hl, hd, msgMap] at h; fin1)
          cases na <;> by_cases hp : pe = ADVERSARY <;>
            simp [hl, hd, msgMap, hp] at h <;> (try split_ifs at h) <;> fin1
      · cases msg <;> try (simp [hl] at h; fin1)
        rename_i na2 nb resp
        cases na <;> cases na2 <;> cases nb <;> by_cases hp : pe = ADVERSARY <;>
          simp [hl, hp] at h <;> (try split_ifs at h) <;> fin1
    | Responding ow pe na nb =>
      rcases hl : lookupF b.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd] at h; fin1
        · cases msg <;> try (simp [hl, hd, msgMap] at h; fin1)
          cases nb <;> simp [hl, hd, msgMap] at h <;> (try split_ifs at h) <;> fin1
      · cases msg <;> try (simp [hl] at h; fin1)
        rename_i nb2
        cases nb <;> cases nb2 <;> simp [hl] at h <;> (try split_ifs at h) <;> fin1
    | Initiated => simp at h; fin1
    | Responded => simp at h; fin1

set_option maxHeartbeats 1000000 in
/-- The ideal step increments each counter at most once. -/
theorem idealStep_facts {Seed Coins Pk Sk Ct : Type _} (F : PkeF Seed Coins Pk Sk Ct)
    (t u : TapeF Seed Coins) (lowe : Bool) (a : IdA Ct) (s : List (Session Std.U64))
    (act : Action Ct) (r : Response Ct) (a' : IdA Ct) (s' : List (Session Std.U64))
    (h : pstep (idealEnv F t u) lowe a s act = (r, a', s')) :
    a'.count ≤ a.count + 1 ∧ a'.ocount ≤ a.ocount + 1 ∧ a'.table.length ≤ a.table.length + 1 := by
  cases act with
  | Start o p =>
    simp only [pstep, idealEnv] at h
    by_cases ho : o = ADVERSARY <;> by_cases hp : p = ADVERSARY <;> simp [ho, hp] at h <;> fin1
  | Respond o m =>
    simp only [pstep, idealEnv] at h
    by_cases ho : o = ADVERSARY
    · simp [ho] at h; fin1
    simp only [ho, ite_false] at h
    rcases hl : lookupF a.table o m with _ | msg
    · rcases hd : F.dec (F.keygen (u.seed o)).2 m with _ | msg
      · simp [hl, hd] at h; fin1
      · cases msg <;> try (simp [hl, hd] at h; fin1)
        rename_i peer
        by_cases hp : peer = ADVERSARY <;> simp [hl, hd, hp] at h <;> fin1
    · cases msg <;> try (simp [hl] at h; fin1)
      rename_i na peer
      by_cases hp : peer = ADVERSARY <;> simp [hl, hp] at h <;> fin1
  | Deliver k m =>
    simp only [pstep, idealEnv] at h
    by_cases hk : k.val < s.length
    swap
    · simp [hk] at h; fin1
    simp only [hk, _root_.dite_true] at h
    obtain ⟨sk, hs⟩ : ∃ sk, s[k.val] = sk := ⟨_, rfl⟩
    simp only [hs] at h
    cases sk with
    | Initiating ow pe na =>
      rcases hl : lookupF a.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd] at h; fin1
        · cases msg <;> try (simp [hl, hd] at h; fin1)
          by_cases hp : pe = ADVERSARY <;> simp [hl, hd, hp] at h <;> (try split_ifs at h) <;> fin1
      · cases msg <;> try (simp [hl] at h; fin1)
        by_cases hp : pe = ADVERSARY <;> simp [hl, hp] at h <;> (try split_ifs at h) <;> fin1
    | Responding ow pe na nb =>
      rcases hl : lookupF a.table ow m with _ | msg
      · rcases hd : F.dec (F.keygen (u.seed ow)).2 m with _ | msg
        · simp [hl, hd] at h; fin1
        · cases msg <;> try (simp [hl, hd] at h; fin1)
          simp [hl, hd] at h; (try split_ifs at h) <;> fin1
      · cases msg <;> try (simp [hl] at h; fin1)
        simp [hl] at h; (try split_ifs at h) <;> fin1
    | Initiated => simp at h; fin1
    | Responded => simp at h; fin1

end examples.nsl.Model
