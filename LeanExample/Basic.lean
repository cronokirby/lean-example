/-!
# A small tour of Lean 4

Open this file in Helix with `lean-tui` running in another terminal, put the
cursor inside a proof, and press `space k` to see the proof state.
Type `\forall`, `\to`, `\and`, `\<>` ... to get the matching Unicode symbols.
-/

namespace LeanExample

def hello := "world"

/-- A binary tree with values at the nodes. -/
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr

namespace Tree

theorem proof : 1 = 1 := by
    let x : Nat := 2
    let y : Nat := 2
    rfl

/-- Number of values stored in the tree. -/
def size : Tree α → Nat
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

/-- Swap the left and right subtrees everywhere. -/
def mirror : Tree α → Tree α
  | leaf => leaf
  | node l x r => node r.mirror x l.mirror

/-- In-order traversal. -/
def toList : Tree α → List α
  | leaf => []
  | node l x r => l.toList ++ [x] ++ r.toList

/-- Insert into a binary search tree. -/
def insert (t : Tree Nat) (v : Nat) : Tree Nat :=
  match t with
  | leaf => node leaf v leaf
  | node l x r =>
    if v < x then node (l.insert v) x r
    else if x < v then node l x (r.insert v)
    else t

def ofList (xs : List Nat) : Tree Nat :=
  xs.foldl insert leaf

theorem size_mirror (t : Tree α) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    let x := 1
    simp only [mirror, size, ihl, ihr]
    omega

theorem mirror_mirror (t : Tree α) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr => simp [mirror, ihl, ihr]

theorem toList_length (t : Tree α) : t.toList.length = t.size := by
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    simp [toList, size, ihl, ihr]
    omega

end Tree

/-- A tactic proof that mixes several connectives. -/
theorem and_or_distrib (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

/-- A term-style proof. -/
theorem exists_gt (n : Nat) : ∃ m, n < m := ⟨n + 1, Nat.lt_succ_self n⟩

theorem sum_formula (n : Nat) : 2 * (List.range (n + 1)).sum = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton, Nat.mul_add, ih]
    grind

end LeanExample
