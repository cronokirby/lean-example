module

public import Examples.Merkle.Lawful
import Examples.Merkle.Completeness
import Examples.Merkle.Binding

/-! # What is proved about the Merkle tree

This module is the audit surface: it states every theorem we prove about
`examples/src/merkle.rs`, and it is the only proof module that `Examples`
exports. The proofs live in `Examples.Merkle.*`, which this module imports
privately, so nothing from them leaks into the public API.

To audit, read:
* the Rust property functions `completeness` and `binding` (and `extract`,
  `is_collision`, `bytes_eq`) in `examples/src/merkle.rs`, whose Aeneas
  translations in `Examples.Gen.Funs` the theorems below are about;
* `Hash.Lawful` in `Examples.Merkle.Lawful`, the only assumption on the hash;
* the statements below.

Each theorem says the property function returns `ok true`: it returns `true`
and, since Aeneas models panics and overflow as errors, never panics.
-/

public section

open Aeneas Aeneas.Std Result

namespace examples.merkle

/-- **Completeness.** For every list of leaves `data` and every `index` into
it, the tree built from `data` has a root, the proof it produces for `index`
verifies against that root with the true size, and none of this panics. An
out-of-range `index` makes `completeness` return `true` trivially. -/
theorem completeness_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness H data index = ok true :=
  Completeness.completeness_spec H hH data index

/-- **Binding.** Two proofs that verify against the same `root` and `index`,
for different data, yield a collision in `H` (a `Collision` that
`is_collision` accepts). This holds even if each proof is checked against a
different claimed tree size `n1`, `n2`, so the size need not be trusted. -/
theorem binding_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding H root index n1 d1 p1 n2 d2 p2 = ok true :=
  Binding.binding_spec H hH root index n1 d1 p1 n2 d2 p2

end examples.merkle
