module

public import Examples.Gen.Funs

/-! Assumptions about the `Hash` implementation that the Merkle proofs rely on.

The Rust trait methods become fields of `merkle.Hash`, each returning a
`Result`. The proofs need the hash functions to never fail, and `==` and `!=`
on digests to decide equality. Nothing else is assumed about `H`; in
particular, collision resistance is not an assumption: binding is stated as
"either the proofs agree, or we can exhibit a collision".
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace examples.merkle

open Classical in
/-- A `Hash` implementation whose functions are total and whose digest
equality is real equality. -/
structure Hash.Lawful {Hs : Type _} {D : Type _} (H : Hash Hs D) : Prop where
  leaf_ok : ∀ s, ∃ d, H.leaf s = ok d
  node_ok : ∀ a b, ∃ d, H.node a b = ok d
  size_ok : ∀ a n, ∃ d, H.size a n = ok d
  eq_ok : ∀ a b : D, H.corecmpEqInst.partialEqInst.eq a b = ok (decide (a = b))
  ne_ok : ∀ a b : D, H.corecmpEqInst.partialEqInst.ne a b = ok (decide (a ≠ b))

end examples.merkle
