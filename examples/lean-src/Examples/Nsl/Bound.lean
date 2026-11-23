module

public import Examples.Nsl.Probability
import Examples.Nsl.Probability.Coupling
import Examples.Nsl.Probability.Counting

/-! # The concrete security bound for NSL secrecy

The game hops, for every total `Pke` with finite `Seed` and `Coins`, every
adversary (any `Adversary` instance with any initial state) and every query
bound `q`, with both tapes uniform (see `Examples.Nsl.Probability`):

1. **Real → ideal** (`game_hop`): the real and the ideal secrecy games are the
   reduction `reduction E Adv adv lowe q` (the secrecy game with the oracle
   left abstract) run with `RealOracle` and with `IdealOracle`, so their
   winning probabilities differ by exactly the multi-user IND-CCA advantage
   of that reduction.
2. **Ideal → bad event** (`idealWin_le`, in
   `Examples.Nsl.Probability.Counting`): with Lowe's fix, winning the ideal
   game means the nonce of the named session `j` is one of at most `q + 1`
   values computed without it (the symbolic run's comparisons with the secret
   and the final guess), which has probability at most `(q + 1) / 2^64`;
   summing over the `q` sessions gives `q (q + 1) / 2^64`.

`secrecy_bound` combines them.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl.Game

variable {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]

theorem fst_eq_ok_true {X : Type} (m : Result (Bool × X)) :
    (do let (b, _) ← m; ok b) = ok true ↔ ∃ x, m = ok (true, x) := by
  constructor
  · intro h
    obtain ⟨⟨b, x⟩, hm, hb⟩ := bind_inv h
    have hb' : b = true := by
      have : (ok b : Result Bool) = ok true := hb
      simpa using this
    exact ⟨x, by rw [hm, hb']⟩
  · rintro ⟨x, hm⟩
    rw [hm]
    simp only [bind_ok]
    rfl

/-- The real game is the reduction run with the real oracle. -/
public theorem realWin_eq (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (qu : Std.Usize) :
    realWin E Adv adv lowe qu = ccaReal E qu.val (reduction E Adv adv lowe qu) := by
  unfold realWin ccaReal reduction
  congr 1
  funext ω
  apply propext
  simp only [RealOracle.new, bind_ok]
  exact (fst_eq_ok_true _).symm

/-- The ideal game is the reduction run with the ideal oracle. -/
public theorem idealWin_eq (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (qu : Std.Usize) :
    idealWin E Adv adv lowe qu = ccaIdeal E qu.val (reduction E Adv adv lowe qu) := by
  unfold idealWin ccaIdeal reduction
  congr 1
  funext ω
  apply propext
  simp only [IdealOracle.new, RealOracle.new, bind_ok]
  exact (fst_eq_ok_true _).symm

/-- **The IND-CCA hop.** The real and ideal secrecy games differ by exactly
the multi-user IND-CCA advantage of the reduction. -/
public theorem game_hop (E : Pke P Seed Coins Pk Sk Ct) (Adv : Adversary A Pk Sk Ct) (adv : A)
    (lowe : Bool) (qu : Std.Usize) :
    |realWin E Adv adv lowe qu - idealWin E Adv adv lowe qu| =
      advCCA E qu.val (reduction E Adv adv lowe qu) := by
  rw [realWin_eq, idealWin_eq]; rfl

/-- **Secrecy of NSL.** For every total `Pke` with finite seed and coin
types, every adversary and every query bound `q`, the adversary wins the real
secrecy game (with Lowe's fix) with probability at most the multi-user IND-CCA
advantage of the reduction plus `q (q + 1) / 2^64`. -/
public theorem secrecy_bound {E : Pke P Seed Coins Pk Sk Ct} (hE : E.Total)
    (Adv : Adversary A Pk Sk Ct) (adv : A) (qu : Std.Usize) :
    realWin E Adv adv true qu ≤
      advCCA E qu.val (reduction E Adv adv true qu) + (qu.val * (qu.val + 1) : ℝ) / 2 ^ 64 := by
  have h1 := game_hop E Adv adv true qu
  have h2 := idealWin_le Adv hE adv qu
  have h3 := le_abs_self (realWin E Adv adv true qu - idealWin E Adv adv true qu)
  linarith

end examples.nsl.Game
