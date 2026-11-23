module

public import Examples.Gen.Funs

/-! # The secrecy invariant of NSL, on plain lists

This module states, without any Aeneas code, where the secret nonce
`Sym.Secret` can be after any run of the protocol with Lowe's check, and
proves that every protocol step preserves it.

`PStep` abstracts one call of `nsl.step` in the symbolic world to its effect
on the secret-relevant state: whether the secret leaked, the table of
ciphertexts encrypted to honest agents, and the sessions. `Inv` is the
invariant. With `σ` the index of the session whose nonce is the secret:

* `before`: session `σ` does not exist yet, so the secret appears nowhere.
* `dishonest`: session `σ`'s peer is the adversary. Anything may happen.
* `ini`: session `σ` is an initiator owned by `a` with honest peer `b`. The
  secret is its `na`; it appears only in `One(Secret, a)` addressed to `b`,
  in `Two(Secret, nb, b)` addressed to `a`, and in responders of `b` with
  peer `a` that took it as `na`.
* `resp`: session `σ` is a responder owned by `b` with honest peer `a`. The
  secret is its `nb`; it appears only in `Two(na, Secret, b)` addressed to
  `a`, in `Three(Secret)` addressed to `b`, and in initiators of `a` with
  peer `b` that took it as `nb`. Lowe's check is what forces these
  initiators' peer to be `b`.

In the last three cases nothing mentioning the secret is ever encrypted to
the adversary, so `leaked` stays false.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace examples.nsl.Secrecy

variable {Ct : Type _}

/-- The message does not mention the secret. -/
def msgClean : Msg Sym → Prop
  | .One a _ => a ≠ .Secret
  | .Two a b _ => a ≠ .Secret ∧ b ≠ .Secret
  | .Three a => a ≠ .Secret

/-- The session does not hold the secret. -/
def sessClean : Session Sym → Prop
  | .Initiating _ _ na => na ≠ .Secret
  | .Initiated _ _ na nb => na ≠ .Secret ∧ nb ≠ .Secret
  | .Responding _ _ na nb => na ≠ .Secret ∧ nb ≠ .Secret
  | .Responded _ _ na nb => na ≠ .Secret ∧ nb ≠ .Secret

/-- The peer of a session. -/
def peerOf : Session Sym → Std.U8
  | .Initiating _ p _ => p
  | .Initiated _ p _ _ => p
  | .Responding _ p _ _ => p
  | .Responded _ p _ _ => p

/-- Session `j` when session `σ` is an initiator owned by `a` with peer `b`. -/
def iniSess (σ : Nat) (a b : Std.U8) (j : Nat) (s : Session Sym) : Prop :=
  (j = σ → s = .Initiating a b .Secret ∨ ∃ nb, s = .Initiated a b .Secret nb) ∧
  (j ≠ σ → sessClean s ∨
    ∃ nb, nb ≠ .Secret ∧ (s = .Responding b a .Secret nb ∨ s = .Responded b a .Secret nb))

/-- A table entry when session `σ` is an initiator owned by `a` with peer `b`. -/
def iniEntry (a b : Std.U8) (e : Entry Ct Sym) : Prop :=
  msgClean e.msg ∨ (e.to = b ∧ e.msg = .One .Secret a) ∨
    (e.to = a ∧ ∃ nb, nb ≠ .Secret ∧ e.msg = .Two .Secret nb b)

/-- Session `j` when session `σ` is a responder owned by `b` with peer `a`. -/
def respSess (σ : Nat) (a b : Std.U8) (j : Nat) (s : Session Sym) : Prop :=
  (j = σ → ∃ na, na ≠ .Secret ∧ (s = .Responding b a na .Secret ∨ s = .Responded b a na .Secret)) ∧
  (j ≠ σ → sessClean s ∨ ∃ na, na ≠ .Secret ∧ s = .Initiated a b na .Secret)

/-- A table entry when session `σ` is a responder owned by `b` with peer `a`. -/
def respEntry (a b : Std.U8) (e : Entry Ct Sym) : Prop :=
  msgClean e.msg ∨ (e.to = a ∧ ∃ na, na ≠ .Secret ∧ e.msg = .Two na .Secret b) ∨
    (e.to = b ∧ e.msg = .Three .Secret)

/-- Every session satisfies `P` at its index. -/
def AllS (P : Nat → Session Sym → Prop) (ss : List (Session Sym)) : Prop :=
  ∀ j s, ss[j]? = some s → P j s

/-- The secrecy invariant; see the module docstring. -/
inductive Inv (σ : Nat) : Bool → List (Entry Ct Sym) → List (Session Sym) → Prop
  | before {tab ss} : ss.length ≤ σ → (∀ s ∈ ss, sessClean s) → (∀ e ∈ tab, msgClean e.msg) →
      Inv σ false tab ss
  | dishonest {l tab ss s} : ss[σ]? = some s → peerOf s = ADVERSARY → Inv σ l tab ss
  | ini {tab ss a b} : a ≠ ADVERSARY → b ≠ ADVERSARY → σ < ss.length →
      AllS (iniSess σ a b) ss → (∀ e ∈ tab, iniEntry a b e) → Inv σ false tab ss
  | resp {tab ss a b} : a ≠ ADVERSARY → b ≠ ADVERSARY → σ < ss.length →
      AllS (respSess σ a b) ss → (∀ e ∈ tab, respEntry a b e) → Inv σ false tab ss

/-- The nonce of a new session: the secret for session `σ`, a value otherwise. -/
def fresh (σ : Nat) (ss : List (Session Sym)) (x : Std.U64) : Sym :=
  if ss.length = σ then .Secret else .Val x

/-- A message `who` may obtain by decryption: a table entry addressed to
`who`, or a message without the secret (a fresh decryption). -/
def decOk (tab : List (Entry Ct Sym)) (who : Std.U8) (m : Msg Sym) : Prop :=
  (∃ e ∈ tab, e.to = who ∧ e.msg = m) ∨ msgClean m

/-- The effect of encrypting `m` to `to` (with ciphertext `ct`) on the leaked
flag and the table. -/
def sent (dst : Std.U8) (m : Msg Sym) (ct : Ct) (l : Bool) (tab : List (Entry Ct Sym))
    (l' : Bool) (tab' : List (Entry Ct Sym)) : Prop :=
  (dst = ADVERSARY → (l' = true → l = true ∨ ¬ msgClean m) ∧ tab' = tab) ∧
  (dst ≠ ADVERSARY → l' = l ∧ tab' = tab ++ [⟨dst, ct, m⟩])

/-- One protocol step with Lowe's check, abstracted to the secret-relevant
state (leaked flag, table, sessions). -/
inductive PStep (σ : Nat) :
    Bool → List (Entry Ct Sym) → List (Session Sym) →
    Bool → List (Entry Ct Sym) → List (Session Sym) → Prop
  | skip {l tab ss} : PStep σ l tab ss l tab ss
  | start {l tab ss l' tab'} (owner peer : Std.U8) (x : Std.U64) (ct : Ct) : owner ≠ ADVERSARY →
      sent peer (.One (fresh σ ss x) owner) ct l tab l' tab' →
      PStep σ l tab ss l' tab' (ss ++ [.Initiating owner peer (fresh σ ss x)])
  | respond {l tab ss l' tab'} (owner peer : Std.U8) (na : Sym) (x : Std.U64) (ct : Ct) : owner ≠ ADVERSARY →
      decOk tab owner (.One na peer) →
      sent peer (.Two na (fresh σ ss x) owner) ct l tab l' tab' →
      PStep σ l tab ss l' tab' (ss ++ [.Responding owner peer na (fresh σ ss x)])
  | deliverI {l tab ss l' tab'} (j : Nat) (owner peer : Std.U8) (na nb : Sym) (ct : Ct) :
      ss[j]? = some (.Initiating owner peer na) →
      decOk tab owner (.Two na nb peer) →
      sent peer (.Three nb) ct l tab l' tab' →
      PStep σ l tab ss l' tab' (ss.set j (.Initiated owner peer na nb))
  | deliverR {l tab ss} (j : Nat) (owner peer : Std.U8) (na nb : Sym) :
      ss[j]? = some (.Responding owner peer na nb) →
      decOk tab owner (.Three nb) →
      PStep σ l tab ss l tab (ss.set j (.Responded owner peer na nb))

/-! ## Preservation -/

theorem AllS_append {P : Nat → Session Sym → Prop} {ss : List (Session Sym)} {x : Session Sym}
    (h : AllS P ss) (hx : P ss.length x) : AllS P (ss ++ [x]) := by
  intro j s hj
  rw [List.getElem?_append] at hj
  split at hj
  · exact h j s hj
  · rw [List.getElem?_singleton] at hj
    split at hj
    · cases hj; grind
    · cases hj

theorem AllS_set {P : Nat → Session Sym → Prop} {ss : List (Session Sym)} {j : Nat}
    {x : Session Sym} (h : AllS P ss) (hx : P j x) : AllS P (ss.set j x) := by
  intro i s hi
  rw [List.getElem?_set] at hi
  split at hi
  · subst i; split at hi
    · cases hi; exact hx
    · cases hi
  · exact h i s hi

theorem AllS_of_forall {P : Nat → Session Sym → Prop} {ss : List (Session Sym)}
    (h : ∀ j s, s ∈ ss → j < ss.length → P j s) : AllS P ss := by
  intro j s hj
  have := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hl, rfl⟩ := this
  exact h j _ (List.getElem_mem _) hl

theorem mem_of_getElem? {ss : List (Session Sym)} {j : Nat} {s : Session Sym}
    (h : ss[j]? = some s) : s ∈ ss := List.mem_of_getElem? h

end examples.nsl.Secrecy


namespace examples.nsl.Secrecy
variable {Ct : Type _}

theorem dishonest_step {σ : Nat} {l l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss ss' : List (Session Sym)} {s : Session Sym}
    (hs : ss[σ]? = some s) (hp : peerOf s = ADVERSARY) (h : PStep σ l tab ss l' tab' ss') :
    Inv σ l' tab' ss' := by
  have hlt : σ < ss.length := (List.getElem?_eq_some_iff.mp hs).1
  cases h with
  | skip => exact .dishonest hs hp
  | start =>
    exact .dishonest (s := s) (by rw [List.getElem?_append_left hlt]; exact hs) hp
  | respond =>
    exact .dishonest (s := s) (by rw [List.getElem?_append_left hlt]; exact hs) hp
  | deliverI j owner peer na nb _ hj _ _ =>
    by_cases hjσ : j = σ
    · subst hjσ
      rw [hs] at hj; cases hj
      exact .dishonest (s := .Initiated owner peer na nb)
        (by rw [List.getElem?_set_self hlt]) (by simpa [peerOf] using hp)
    · exact .dishonest (s := s) (by rw [List.getElem?_set_ne hjσ]; exact hs) hp
  | deliverR j owner peer na nb hj _ =>
    by_cases hjσ : j = σ
    · subst hjσ
      rw [hs] at hj; cases hj
      exact .dishonest (s := .Responded owner peer na nb)
        (by rw [List.getElem?_set_self hlt]) (by simpa [peerOf] using hp)
    · exact .dishonest (s := s) (by rw [List.getElem?_set_ne hjσ]; exact hs) hp

theorem before_step {σ : Nat} {l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss ss' : List (Session Sym)} (hlen : ss.length ≤ σ) (hss : ∀ s ∈ ss, sessClean s)
    (htab : ∀ e ∈ tab, msgClean e.msg) (h : PStep σ false tab ss l' tab' ss') :
    Inv σ l' tab' ss' := by
  have dec : ∀ who m, decOk tab who m → msgClean m := by
    intro who m hm; rcases hm with ⟨e, he, -, rfl⟩ | hm
    · exact htab e he
    · exact hm
  cases h with
  | skip => exact .before hlen hss htab
  | start owner peer x ct hown hsent =>
    by_cases hσ : ss.length = σ
    · have hf : fresh σ ss x = .Secret := by simp [fresh, hσ]
      rw [hf] at hsent ⊢
      by_cases hp : peer = ADVERSARY
      · exact .dishonest (s := .Initiating owner peer .Secret)
          (by rw [← hσ]; simp) (by simp [peerOf, hp])
      · obtain ⟨rfl, rfl⟩ := hsent.2 hp
        refine .ini (a := owner) (b := peer) hown hp (by simp; omega) ?_ ?_
        · refine AllS_append (AllS_of_forall ?_) ?_
          · intro j s hs hj; exact ⟨by omega, fun _ => .inl (hss s hs)⟩
          · exact ⟨fun _ => .inl rfl, fun h => absurd hσ h⟩
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact .inl (htab e he)
          · exact .inr (.inl ⟨rfl, rfl⟩)
    · have hf : fresh σ ss x = .Val x := by simp [fresh, hσ]
      rw [hf] at hsent ⊢
      have hl' : l' = false := by
        by_cases hp : peer = ADVERSARY
        · have := (hsent.1 hp).1; cases l' <;> simp_all [msgClean]
        · exact (hsent.2 hp).1
      subst hl'
      refine .before (by simp; omega) ?_ ?_
      · intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hss s hs
        · simp [sessClean]
      · intro e he
        by_cases hp : peer = ADVERSARY
        · rw [(hsent.1 hp).2] at he; exact htab e he
        · rw [(hsent.2 hp).2] at he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact htab e he
          · simp [msgClean]
  | respond owner peer na x ct hown hdec hsent =>
    have hna : na ≠ .Secret := dec _ _ hdec
    by_cases hσ : ss.length = σ
    · have hf : fresh σ ss x = .Secret := by simp [fresh, hσ]
      rw [hf] at hsent ⊢
      by_cases hp : peer = ADVERSARY
      · exact .dishonest (s := .Responding owner peer na .Secret)
          (by rw [← hσ]; simp) (by simp [peerOf, hp])
      · obtain ⟨rfl, rfl⟩ := hsent.2 hp
        refine .resp (a := peer) (b := owner) hp hown (by simp; omega) ?_ ?_
        · refine AllS_append (AllS_of_forall ?_) ?_
          · intro j s hs hj; exact ⟨by omega, fun _ => .inl (hss s hs)⟩
          · exact ⟨fun _ => ⟨na, hna, .inl rfl⟩, fun h => absurd hσ h⟩
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact .inl (htab e he)
          · exact .inr (.inl ⟨rfl, na, hna, rfl⟩)
    · have hf : fresh σ ss x = .Val x := by simp [fresh, hσ]
      rw [hf] at hsent ⊢
      have hl' : l' = false := by
        by_cases hp : peer = ADVERSARY
        · have := (hsent.1 hp).1; cases l' <;> simp_all [msgClean]
        · exact (hsent.2 hp).1
      subst hl'
      refine .before (by simp; omega) ?_ ?_
      · intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hss s hs
        · simp [sessClean, hna]
      · intro e he
        by_cases hp : peer = ADVERSARY
        · rw [(hsent.1 hp).2] at he; exact htab e he
        · rw [(hsent.2 hp).2] at he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact htab e he
          · simp [msgClean, hna]
  | deliverI j owner peer na nb ct hj hdec hsent =>
    have hm : msgClean (.Two na nb peer) := dec _ _ hdec
    simp only [msgClean] at hm
    have hl' : l' = false := by
      by_cases hp : peer = ADVERSARY
      · have := (hsent.1 hp).1; cases l' <;> simp_all [msgClean]
      · exact (hsent.2 hp).1
    subst hl'
    refine .before (by simp; omega) ?_ ?_
    · intro s hs
      rcases List.mem_or_eq_of_mem_set hs with hs | rfl
      · exact hss s hs
      · simp [sessClean, hm]
    · intro e he
      by_cases hp : peer = ADVERSARY
      · rw [(hsent.1 hp).2] at he; exact htab e he
      · rw [(hsent.2 hp).2] at he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact htab e he
        · simp [msgClean, hm]
  | deliverR j owner peer na nb hj hdec =>
    have hs0 := hss _ (List.mem_of_getElem? hj)
    refine .before (by simp; omega) ?_ htab
    intro s hs
    rcases List.mem_or_eq_of_mem_set hs with hs | rfl
    · exact hss s hs
    · simpa [sessClean] using hs0

end examples.nsl.Secrecy


namespace examples.nsl.Secrecy
variable {Ct : Type _}

theorem sent_inv {dst : Std.U8} {m : Msg Sym} {ct : Ct} {tab tab' : List (Entry Ct Sym)} {l' : Bool}
    (h : sent dst m ct false tab l' tab') (hc : dst = ADVERSARY → msgClean m) :
    l' = false ∧ ∀ e ∈ tab', e ∈ tab ∨ (dst ≠ ADVERSARY ∧ e = ⟨dst, ct, m⟩) := by
  by_cases hd : dst = ADVERSARY
  · obtain ⟨h1, rfl⟩ := h.1 hd
    refine ⟨?_, fun e he => .inl he⟩
    cases l' <;> simp_all
  · obtain ⟨rfl, rfl⟩ := h.2 hd
    refine ⟨rfl, fun e he => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact .inl he
    · exact .inr ⟨hd, rfl⟩

theorem ini_step {σ : Nat} {a b : Std.U8} {l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss ss' : List (Session Sym)} (ha : a ≠ ADVERSARY) (hb : b ≠ ADVERSARY)
    (hlt : σ < ss.length) (hS : AllS (iniSess σ a b) ss) (hT : ∀ e ∈ tab, iniEntry a b e)
    (h : PStep σ false tab ss l' tab' ss') :
    Inv σ l' tab' ss' := by
  cases h with
  | skip => exact .ini ha hb hlt hS hT
  | start owner peer x ct hown hsent =>
    have hf : fresh σ ss x = .Val x := by simp [fresh]; omega
    rw [hf] at hsent ⊢
    obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean])
    refine .ini ha hb (by simp; omega) (AllS_append hS ?_) ?_
    · simp [iniSess, sessClean]; omega
    · intro e he
      rcases htab e he with he | ⟨-, rfl⟩
      · exact hT e he
      · exact .inl (by simp [msgClean])
  | respond owner peer na x ct hown hdec hsent =>
    have hf : fresh σ ss x = .Val x := by simp [fresh]; omega
    rw [hf] at hsent ⊢
    have hcase : na ≠ .Secret ∨ (na = .Secret ∧ owner = b ∧ peer = a) := by
      rcases hdec with ⟨e, he, hto, hm⟩ | hm
      · rcases hT e he with hc | ⟨h1, h2⟩ | ⟨h1, nb, -, h2⟩
        · rw [hm] at hc; exact .inl hc
        · rw [hm] at h2; cases h2; exact .inr ⟨rfl, hto ▸ h1, rfl⟩
        · rw [hm] at h2; cases h2
      · exact .inl hm
    rcases hcase with hna | ⟨rfl, rfl, rfl⟩
    · obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean, hna])
      refine .ini ha hb (by simp; omega) (AllS_append hS ?_) ?_
      · simp [iniSess, sessClean, hna]; omega
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inl (by simp [msgClean, hna])
    · obtain ⟨rfl, htab⟩ := sent_inv hsent (fun h => absurd h ha)
      refine .ini ha hb (by simp; omega) (AllS_append hS ?_) ?_
      · simp [iniSess]; omega
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inr (.inr ⟨rfl, .Val x, by simp, rfl⟩)
  | deliverI j owner peer na nb ct hj hdec hsent =>
    have hjs := hS j _ hj
    have hjl : j < ss.length := (List.getElem?_eq_some_iff.mp hj).1
    by_cases hjσ : j = σ
    · obtain ⟨h1, -⟩ := hjs
      rcases h1 hjσ with h1 | ⟨_, h1⟩ <;> cases h1
      have hnb : nb ≠ .Secret := by
        rcases hdec with ⟨e, he, hto, hm⟩ | hm
        · rcases hT e he with hc | ⟨h1, h2⟩ | ⟨h1, nb', hnb', h2⟩
          · rw [hm] at hc; simp [msgClean] at hc
          · rw [hm] at h2; cases h2
          · rw [hm] at h2; cases h2; exact hnb'
        · simp [msgClean] at hm
      obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean, hnb])
      refine .ini ha hb (by simp; omega) (AllS_set hS ?_) ?_
      · simp [iniSess, hjσ]
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inl (by simp [msgClean, hnb])
    · have hna : na ≠ .Secret := by
        rcases hjs.2 hjσ with h1 | ⟨_, _, h1 | h1⟩
        · simpa [sessClean] using h1
        · cases h1
        · cases h1
      have hnb : nb ≠ .Secret := by
        rcases hdec with ⟨e, he, hto, hm⟩ | hm
        · rcases hT e he with hc | ⟨h1, h2⟩ | ⟨h1, nb', hnb', h2⟩
          · rw [hm] at hc; simp [msgClean] at hc; exact hc.2
          · rw [hm] at h2; cases h2
          · rw [hm] at h2; cases h2; exact absurd rfl hna
        · simp [msgClean] at hm; exact hm.2
      obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean, hnb])
      refine .ini ha hb (by simp; omega) (AllS_set hS ?_) ?_
      · simp [iniSess, hjσ, sessClean, hna, hnb]
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inl (by simp [msgClean, hnb])
  | deliverR j owner peer na nb hj hdec =>
    have hjs := hS j _ hj
    refine .ini ha hb (by simp; omega) (AllS_set hS ?_) hT
    by_cases hjσ : j = σ
    · rcases hjs.1 hjσ with h1 | ⟨_, h1⟩ <;> cases h1
    · refine ⟨fun h => absurd h hjσ, fun _ => ?_⟩
      rcases hjs.2 hjσ with h1 | ⟨nb', hnb', h1 | h1⟩
      · exact .inl (by simpa [sessClean] using h1)
      · cases h1; exact .inr ⟨_, hnb', .inr rfl⟩
      · cases h1

theorem resp_step {σ : Nat} {a b : Std.U8} {l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss ss' : List (Session Sym)} (ha : a ≠ ADVERSARY) (hb : b ≠ ADVERSARY)
    (hlt : σ < ss.length) (hS : AllS (respSess σ a b) ss) (hT : ∀ e ∈ tab, respEntry a b e)
    (h : PStep σ false tab ss l' tab' ss') :
    Inv σ l' tab' ss' := by
  cases h with
  | skip => exact .resp ha hb hlt hS hT
  | start owner peer x ct hown hsent =>
    have hf : fresh σ ss x = .Val x := by simp [fresh]; omega
    rw [hf] at hsent ⊢
    obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean])
    refine .resp ha hb (by simp; omega) (AllS_append hS ?_) ?_
    · simp [respSess, sessClean]; omega
    · intro e he
      rcases htab e he with he | ⟨-, rfl⟩
      · exact hT e he
      · exact .inl (by simp [msgClean])
  | respond owner peer na x ct hown hdec hsent =>
    have hf : fresh σ ss x = .Val x := by simp [fresh]; omega
    rw [hf] at hsent ⊢
    have hna : na ≠ .Secret := by
      rcases hdec with ⟨e, he, hto, hm⟩ | hm
      · rcases hT e he with hc | ⟨h1, _, _, h2⟩ | ⟨h1, h2⟩
        · rw [hm] at hc; exact hc
        · rw [hm] at h2; cases h2
        · rw [hm] at h2; cases h2
      · exact hm
    obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean, hna])
    refine .resp ha hb (by simp; omega) (AllS_append hS ?_) ?_
    · simp [respSess, sessClean, hna]; omega
    · intro e he
      rcases htab e he with he | ⟨-, rfl⟩
      · exact hT e he
      · exact .inl (by simp [msgClean, hna])
  | deliverI j owner peer na nb ct hj hdec hsent =>
    have hjs := hS j _ hj
    have hjσ : j ≠ σ := by
      intro hjσ; obtain ⟨_, _, h1 | h1⟩ := hjs.1 hjσ <;> cases h1
    have hna : na ≠ .Secret := by
      rcases hjs.2 hjσ with h1 | ⟨_, _, h1⟩
      · simpa [sessClean] using h1
      · cases h1
    have hcase : nb ≠ .Secret ∨ (nb = .Secret ∧ owner = a ∧ peer = b) := by
      rcases hdec with ⟨e, he, hto, hm⟩ | hm
      · rcases hT e he with hc | ⟨h1, na', _, h2⟩ | ⟨h1, h2⟩
        · rw [hm] at hc; simp [msgClean] at hc; exact .inl hc.2
        · rw [hm] at h2; cases h2; exact .inr ⟨rfl, hto ▸ h1, rfl⟩
        · rw [hm] at h2; cases h2
      · simp [msgClean] at hm; exact .inl hm.2
    rcases hcase with hnb | ⟨rfl, rfl, rfl⟩
    · obtain ⟨rfl, htab⟩ := sent_inv hsent (fun _ => by simp [msgClean, hnb])
      refine .resp ha hb (by simp; omega) (AllS_set hS ?_) ?_
      · simp [respSess, hjσ, sessClean, hna, hnb]
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inl (by simp [msgClean, hnb])
    · obtain ⟨rfl, htab⟩ := sent_inv hsent (fun h => absurd h hb)
      refine .resp ha hb (by simp; omega) (AllS_set hS ?_) ?_
      · simp [respSess, hjσ, hna]
      · intro e he
        rcases htab e he with he | ⟨-, rfl⟩
        · exact hT e he
        · exact .inr (.inr ⟨rfl, rfl⟩)
  | deliverR j owner peer na nb hj hdec =>
    have hjs := hS j _ hj
    refine .resp ha hb (by simp; omega) (AllS_set hS ?_) hT
    by_cases hjσ : j = σ
    · obtain ⟨na', hna', h1 | h1⟩ := hjs.1 hjσ
      · cases h1; exact ⟨fun _ => ⟨_, hna', .inr rfl⟩, fun h => absurd hjσ h⟩
      · cases h1
    · refine ⟨fun h => absurd h hjσ, fun _ => ?_⟩
      rcases hjs.2 hjσ with h1 | ⟨_, _, h1⟩
      · exact .inl (by simpa [sessClean] using h1)
      · cases h1

/-- Every protocol step with Lowe's check preserves the invariant. -/
theorem Inv.step {σ : Nat} {l l' : Bool} {tab tab' : List (Entry Ct Sym)}
    {ss ss' : List (Session Sym)} (hi : Inv σ l tab ss) (h : PStep σ l tab ss l' tab' ss') :
    Inv σ l' tab' ss' := by
  cases hi with
  | before hlen hss htab => exact before_step hlen hss htab h
  | dishonest hs hp => exact dishonest_step hs hp h
  | ini ha hb hlt hS hT => exact ini_step ha hb hlt hS hT h
  | resp ha hb hlt hS hT => exact resp_step ha hb hlt hS hT h

/-- The invariant at the start of a run. -/
theorem Inv.nil (σ : Nat) : Inv (Ct := Ct) σ false [] [] :=
  .before (by simp) (by simp) (by simp)

/-- If the secret leaked, session `σ` exists and its peer is the adversary. -/
theorem Inv.leaked {σ : Nat} {tab : List (Entry Ct Sym)} {ss : List (Session Sym)}
    (hi : Inv σ true tab ss) : ∃ s, ss[σ]? = some s ∧ peerOf s = ADVERSARY := by
  cases hi with
  | dishonest hs hp => exact ⟨_, hs, hp⟩

end examples.nsl.Secrecy

