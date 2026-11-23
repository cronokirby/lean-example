module

public import Examples.Nsl.Probability
import Examples.Nsl.Probability.Coupling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Counting

`card_lens_le`: if `get`/`set` is a lens onto a `U64` coordinate of a finite
type `Ω` and `L ω` is a list of at most `m` values that depends on `ω` only
through `set ω 0` (the outcome with that coordinate erased), then the
coordinate lands in `L` with probability at most `m / 2^64`.

`idealWin_le` applies it to each session's nonce and sums over the `q`
sessions the adversary can name: the ideal game is won with probability at
most `q (q + 1) / 2^64`.
-/

open Aeneas Aeneas.Std Result

namespace examples.nsl.Game

open Model

theorem card_lens_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (z : Std.U64) (get : Ω → Std.U64)
    (set : Ω → Std.U64 → Ω) (hgs : ∀ ω m, get (set ω m) = m)
    (hss : ∀ ω m m', set (set ω m) m' = set ω m') (hsg : ∀ ω, set ω (get ω) = ω)
    (L : Ω → List Std.U64) (m : Nat) (hL : ∀ ω, (L ω).length ≤ m)
    [DecidablePred fun ω => get ω ∈ L (set ω z)] :
    (Finset.univ.filter fun ω => get ω ∈ L (set ω z)).card * 2 ^ 64 ≤ m * Fintype.card Ω := by
  classical
  let π : Ω → Ω := fun ω => set ω z
  let T := Finset.univ.image π
  have hrec : ∀ ω, set (π ω) (get ω) = ω := fun ω => by simp only [π, hss, hsg]
  have hT : ∀ x ∈ T, set x z = x := by
    intro x hx
    obtain ⟨ω, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [π, hss]
  -- Each fiber of `π` has 2^64 elements.
  have hfib : ∀ x ∈ T, (Finset.univ.filter fun ω => π ω = x).card = 2 ^ 64 := by
    intro x hx
    have : (Finset.univ.filter fun ω => π ω = x) = Finset.univ.image (set x) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h; exact ⟨get ω, by rw [← h, hrec]⟩
      · rintro ⟨m', rfl⟩; simp only [π, hss]; exact hT x hx
    rw [this, Finset.card_image_of_injective _ (fun a b h => by
      have := congrArg get h; simpa [hgs] using this)]
    simp [card_u64]
  -- In each fiber the event has at most `m` elements.
  have hev : ∀ x ∈ T,
      ((Finset.univ.filter fun ω => get ω ∈ L (set ω z)).filter fun ω => π ω = x).card ≤ m := by
    intro x _
    calc _ ≤ (L x).toFinset.card := by
          apply Finset.card_le_card_of_injOn get
          · intro ω hω
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hω
            simp only [Finset.mem_coe, List.mem_toFinset]
            rw [← hω.2]; exact hω.1
          · intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at ha hb
            rw [← hrec a, ← hrec b, ha.2, hb.2, hab]
      _ ≤ (L x).length := List.toFinset_card_le _
      _ ≤ m := hL x
  have h1 := Finset.card_eq_sum_card_fiberwise (f := π) (t := T)
    (s := Finset.univ.filter fun ω => get ω ∈ L (set ω z))
    (fun ω _ => Finset.mem_image_of_mem π (Finset.mem_univ ω))
  have h2 := Finset.card_eq_sum_card_fiberwise (f := π) (t := T) (s := Finset.univ)
    (fun ω _ => Finset.mem_image_of_mem π (Finset.mem_univ ω))
  have h3 : (Finset.univ.filter fun ω => get ω ∈ L (set ω z)).card ≤ T.card * m := by
    rw [h1]
    calc _ ≤ ∑ _x ∈ T, m := Finset.sum_le_sum hev
      _ = T.card * m := by simp
  have h4 : Fintype.card Ω = T.card * 2 ^ 64 := by
    rw [← Finset.card_univ, h2, Finset.sum_congr rfl hfib]
    simp
  rw [h4]
  calc _ ≤ T.card * m * 2 ^ 64 := Nat.mul_le_mul_right _ h3
    _ = m * (T.card * 2 ^ 64) := by ring

variable {P Seed Coins Pk Sk Ct A : Type} [Fintype Seed] [Fintype Coins]

omit [Fintype Seed] [Fintype Coins] in
theorem idealOracle_new (E : Pke P Seed Coins Pk Sk Ct) {q : Nat} (ot : GameTape Seed Coins q) :
    IdealOracle.new E (gameTape Seed Coins q) ot = ok (idealOracle P ot) := by
  simp [IdealOracle.new, RealOracle.new, idealOracle]

/-- **The ideal game.** With Lowe's fix, the adversary wins the ideal secrecy
game with probability at most `q (q + 1) / 2^64`. -/
public theorem idealWin_le {E : Pke P Seed Coins Pk Sk Ct} (Adv : Adversary A Pk Sk Ct)
    (hE : E.Total) (adv : A) (qu : Std.Usize) :
    idealWin E Adv adv true qu ≤ (qu.val * (qu.val + 1) : ℝ) / 2 ^ 64 := by
  classical
  let q := qu.val
  let Win : Outcome Seed Coins q → Prop := fun ω =>
    ∃ adv', (do
      let o ← IdealOracle.new E (gameTape Seed Coins q) ω.2
      secrecy_game E (gameTape Seed Coins q)
        (IdealOracle.Insts.ExamplesNslOracle E (gameTape Seed Coins q)) Adv true ω.1 o adv qu) =
      ok (true, adv')
  let Ej : Fin q → Outcome Seed Coins q → Prop := fun j ω =>
    ω.1.nonces j ∈ badList E Adv adv qu (natU j.val) (erase j ω.1) ω.2
  -- Winning means hitting some session's bad list.
  have hsub : (Finset.univ.filter Win) ⊆ Finset.univ.biUnion fun j => Finset.univ.filter (Ej j) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Win, idealOracle_new, bind_ok] at hω
    obtain ⟨a', h⟩ := hω
    obtain ⟨j, hj⟩ := ideal_win_bad Adv hE adv qu ω.1 ω.2 a' h
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨j, hj⟩
  -- Each session's bad list is hit with probability at most (q + 1) / 2^64.
  have hj : ∀ j : Fin q, (Finset.univ.filter (Ej j)).card * 2 ^ 64 ≤
      (q + 1) * Fintype.card (Outcome Seed Coins q) := by
    intro j
    have := card_lens_le (Ω := Outcome Seed Coins q) 0#u64 (fun ω => ω.1.nonces j)
      (fun ω m => ({ ω.1 with nonces := Function.update ω.1.nonces j m }, ω.2))
      (fun ω m => by simp) (fun ω m m' => by simp)
      (fun ω => by simp)
      (fun ω => badList E Adv adv qu (natU j.val) ω.1 ω.2) (q + 1)
      (fun ω => badList_length Adv hE adv qu _ _ _)
    have heq : Finset.univ.filter (Ej j) = Finset.univ.filter (fun ω : Outcome Seed Coins q =>
        ω.1.nonces j ∈ badList E Adv adv qu (natU j.val)
          ({ ω.1 with nonces := Function.update ω.1.nonces j 0#u64 }, ω.2).1
          ({ ω.1 with nonces := Function.update ω.1.nonces j 0#u64 }, ω.2).2) :=
      Finset.filter_congr (fun ω _ => Iff.rfl)
    rw [heq]
    exact this
  have hW : (Finset.univ.filter Win).card * 2 ^ 64 ≤ q * (q + 1) * Fintype.card (Outcome Seed Coins q) := by
    calc (Finset.univ.filter Win).card * 2 ^ 64
        ≤ (∑ j : Fin q, (Finset.univ.filter (Ej j)).card) * 2 ^ 64 :=
          Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
      _ = ∑ j : Fin q, (Finset.univ.filter (Ej j)).card * 2 ^ 64 := Finset.sum_mul _ _ _
      _ ≤ ∑ _j : Fin q, (q + 1) * Fintype.card (Outcome Seed Coins q) := Finset.sum_le_sum fun j _ => hj j
      _ = q * (q + 1) * Fintype.card (Outcome Seed Coins q) := by simp [mul_assoc]
  unfold idealWin prob
  change ((Finset.univ.filter Win).card : ℝ) / Fintype.card (Outcome Seed Coins q) ≤ _
  rcases Nat.eq_zero_or_pos (Fintype.card (Outcome Seed Coins q)) with h0 | h0
  · rw [h0]; simp; positivity
  · rw [div_le_div_iff₀ (by exact_mod_cast h0) (by positivity)]
    exact_mod_cast hW

end examples.nsl.Game
