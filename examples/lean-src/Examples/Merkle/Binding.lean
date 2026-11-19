module

public import Examples.Merkle.Lawful

open Aeneas Aeneas.Std Result

namespace examples.merkle
namespace Binding

theorem spec_result {α : Type _} {m : Result α} {P : α → Prop}
    (h : m ⦃ x => P x ⦄) : ∃ x, m = ok x ∧ P x := by
  cases m using Result.cases with
  | ret x => exact ⟨x, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

@[step] theorem leaf_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (s : Slice U8) : H.leaf s ⦃ (_ : D) => True ⦄ := by
  obtain ⟨d, hd⟩ := hH.leaf_ok s
  simp [hd]

@[step] theorem node_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (a b : D) : H.node a b ⦃ (_ : D) => True ⦄ := by
  obtain ⟨d, hd⟩ := hH.node_ok a b
  simp [hd]

@[step] theorem size_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (a : D) (n : Usize) : H.size a n ⦃ (_ : D) => True ⦄ := by
  obtain ⟨d, hd⟩ := hH.size_ok a n
  simp [hd]

@[step] theorem has_sibling_spec (index width : Usize) (hi : index.val < width.val) :
    has_sibling index width ⦃ (b : Bool) =>
      b = decide (index.val % 2 = 1 ∨ index.val + 1 < width.val) ⦄ := by
  unfold has_sibling
  step*

@[step] theorem parent_width_spec (width : Usize) :
    parent_width width ⦃ (w : Usize) => w.val = width.val / 2 + width.val % 2 ⦄ := by
  unfold parent_width
  step*

@[step] theorem step_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (index : Usize) (a b : D) :
    merkle.step H index a b ⦃ (_ : D) => True ⦄ := by
  unfold merkle.step
  step*

@[step] theorem bytes_eq_loop_spec (a b : Slice U8) (i : Usize)
    (hlen : a.val.length = b.val.length) :
    bytes_eq_loop a b i ⦃ (_ : Bool) => True ⦄ := by
  unfold bytes_eq_loop
  dsimp only
  split
  · step*
  · simp
termination_by a.val.length - i.val
decreasing_by scalar_tac

@[step] theorem bytes_eq_spec (a b : Slice U8) :
    bytes_eq a b ⦃ (_ : Bool) => True ⦄ := by
  unfold bytes_eq
  dsimp only
  split
  · simp
  · step*

@[step] theorem inner_root_loop_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (proof : Slice D) (acc : D) (index width i : Usize)
    (hi : index.val < width.val) :
    inner_root_loop H proof acc index width i ⦃ (_ : Option D) => True ⦄ := by
  unfold inner_root_loop
  split
  · step*
  · step*
termination_by width.val
decreasing_by
  · scalar_tac
  · scalar_tac

@[step] theorem inner_root_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (size index : Usize) (data : Slice U8) (proof : Slice D) :
    inner_root H size index data proof ⦃ (_ : Option D) => True ⦄ := by
  unfold inner_root
  step*

@[step] theorem verify_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (size index : Usize) (data : Slice U8) (proof : Slice D) :
    verify H root size index data proof ⦃ (b : Bool) =>
      b = true → ∃ r, inner_root H size index data proof = ok (some r) ∧
        H.size r size = ok root ⦄ := by
  classical
  obtain ⟨o, ho, _⟩ := spec_result (inner_root_spec H hH size index data proof)
  unfold verify
  rw [ho]
  cases o with
  | none => simp
  | some r =>
    obtain ⟨d, hd⟩ := hH.size_ok r size
    simp [hd, hH.eq_ok]

theorem leaf_collision {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (d1 d2 : Slice U8) (a : D) (he : bytes_eq d1 d2 = ok false)
    (h1 : H.leaf d1 = ok a) (h2 : H.leaf d2 = ok a) :
    is_collision H (.Leaf d1 d2) = ok true := by
  simp [is_collision, he, h1, h2, hH.eq_ok]

theorem size_collision {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (a b root : D) (n m : Usize) (hne : a ≠ b ∨ n ≠ m)
    (h1 : H.size a n = ok root) (h2 : H.size b m = ok root) :
    is_collision H (.Size a n b m) = ok true := by
  classical
  simp [is_collision, hH.ne_ok, hH.eq_ok, h1, h2]
  intro hab hnm
  have hnm' : n = m := by scalar_tac
  exact hne.elim (fun h => h hab) (fun h => h hnm')

theorem node_collision {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (a b c d out : D) (hne : a ≠ c ∨ b ≠ d)
    (h1 : H.node a b = ok out) (h2 : H.node c d = ok out) :
    is_collision H (.Node a b c d) = ok true := by
  classical
  simp [is_collision, hH.ne_ok, hH.eq_ok, h1, h2]
  tauto

/-- The lockstep invariant: both paths terminate in roots with the same size
commitment, while their current accumulators differ. -/
@[step] theorem extract_loop_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (n : Usize) (p1 p2 : Slice D) (a b root r1 r2 : D)
    (index width i : Usize) (hi : index.val < width.val) (hab : a ≠ b)
    (h1 : inner_root_loop H p1 a index width i = ok (some r1))
    (h2 : inner_root_loop H p2 b index width i = ok (some r2))
    (hs1 : H.size r1 n = ok root) (hs2 : H.size r2 n = ok root) :
    extract_loop1 H n p1 n p2 a b index width i ⦃ (o : Option (Collision D)) =>
      ∃ c, o = some c ∧ is_collision H c = ok true ⦄ := by
  classical
  unfold extract_loop1
  by_cases hw : width > 1#usize
  · obtain ⟨sib, hsib, _⟩ := spec_result (has_sibling_spec index width hi)
    obtain ⟨idx, hidx, hidxval⟩ := UScalar.div_spec index (y := 2#usize) (by decide)
    obtain ⟨w, hwstep, hwval⟩ := spec_result (parent_width_spec width)
    have hwlt : w.val < width.val := by scalar_tac
    have hidxlt : idx.val < w.val := by scalar_tac
    unfold inner_root_loop at h1 h2
    simp only [hw, ↓reduceIte, hsib] at h1 h2 ⊢
    cases sib with
    | false =>
      simp [hidx, hwstep] at h1 h2 ⊢
      step with extract_loop_spec H hH n p1 p2 a b root r1 r2 idx w i hidxlt hab h1 h2 hs1 hs2
      agrind
    | true =>
      have hi1 : ¬i ≥ p1.len := by
        intro h
        simp [h] at h1
      have hi2 : ¬i ≥ p2.len := by
        intro h
        simp [h] at h2
      obtain ⟨s1, hs1get, _⟩ := spec_result (Slice.index_usize_spec p1 i (by scalar_tac))
      obtain ⟨s2, hs2get, _⟩ := spec_result (Slice.index_usize_spec p2 i (by scalar_tac))
      obtain ⟨a', ha', _⟩ := spec_result (step_spec H hH index a s1)
      obtain ⟨b', hb', _⟩ := spec_result (step_spec H hH index b s2)
      obtain ⟨j, hj, hjval⟩ := spec_result (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      simp [hi1, hi2, hs1get, hs2get, ha', hb', hj, hidx, hwstep] at h1 h2 ⊢
      simp [hH.ne_ok, hab, hH.eq_ok]
      by_cases hab' : a' = b'
      · subst b'
        obtain ⟨parity, hp, hpval⟩ := spec_result (UScalar.rem_spec index (y := 2#usize) (by decide))
        simp [hp]
        unfold merkle.step at ha' hb'
        simp only [hp, bind_ok] at ha' hb'
        by_cases hp1 : parity = 1#usize
        · simp only [hp1, ↓reduceIte] at ha' hb'
          simpa [hp1] using node_collision H hH s1 a s2 b a' (Or.inr hab) ha' hb'
        · simp only [hp1, ↓reduceIte] at ha' hb'
          simpa [hp1] using node_collision H hH a s1 b s2 a' (Or.inl hab) ha' hb'
      · simp only [hab', ↓reduceIte]
        step with extract_loop_spec H hH n p1 p2 a' b' root r1 r2 idx w j hidxlt hab' h1 h2 hs1 hs2
        agrind
  · unfold inner_root_loop at h1 h2
    simp only [hw, ↓reduceIte] at h1 h2
    split at h1 <;> simp only [Result.ok.injEq, Option.some.injEq, reduceCtorEq] at h1
    subst r1
    split at h2 <;> simp only [Result.ok.injEq, Option.some.injEq, reduceCtorEq] at h2
    subst r2
    simp [hw, hH.ne_ok, hab, size_collision H hH a b root n n (Or.inl hab) hs1 hs2]
termination_by width.val

@[step] theorem extract_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (index n1 : Usize) (d1 : Slice U8) (p1 : Slice D)
    (n2 : Usize) (d2 : Slice U8) (p2 : Slice D)
    (he : bytes_eq d1 d2 = ok false)
    (r1 r2 : D)
    (h1 : inner_root H n1 index d1 p1 = ok (some r1))
    (h2 : inner_root H n2 index d2 p2 = ok (some r2))
    (hs1 : H.size r1 n1 = ok root) (hs2 : H.size r2 n2 = ok root) :
    extract H index n1 d1 p1 n2 d2 p2 ⦃ (o : Option (Collision D)) =>
      ∃ c, o = some c ∧ is_collision H c = ok true ⦄ := by
  classical
  unfold extract
  by_cases hn : n1 = n2
  · subst n2
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨a, ha⟩ := hH.leaf_ok d1
    obtain ⟨b, hb⟩ := hH.leaf_ok d2
    simp only [ha, hb, he, hH.eq_ok]
    by_cases hab : a = b
    · subst b
      simp [leaf_collision H hH d1 d2 a he ha hb]
    · have hi : index.val < n1.val := by
        by_contra hn
        have hge : index ≥ n1 := by scalar_tac
        simp [inner_root, hge] at h1
      have hl1 : inner_root_loop H p1 a index n1 0#usize = ok (some r1) := by
        simpa [inner_root, ha, show ¬index ≥ n1 by scalar_tac] using h1
      have hl2 : inner_root_loop H p2 b index n1 0#usize = ok (some r2) := by
        simpa [inner_root, hb, show ¬index ≥ n1 by scalar_tac] using h2
      simpa [hab] using extract_loop_spec H hH n1 p1 p2 a b root r1 r2 index n1 0#usize hi hab hl1 hl2 hs1 hs2
  · simp [hn, h1, h2, size_collision H hH r1 r2 root n1 n2 (Or.inr hn) hs1 hs2]

public theorem binding_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (root : D) (index n1 : Std.Usize) (d1 : Slice Std.U8) (p1 : Slice D)
    (n2 : Std.Usize) (d2 : Slice Std.U8) (p2 : Slice D) :
    binding H root index n1 d1 p1 n2 d2 p2 = ok true := by
  obtain ⟨be, he, _⟩ := spec_result (bytes_eq_spec d1 d2)
  unfold binding
  rw [he]
  cases be with
  | true => simp
  | false =>
    obtain ⟨v1, hv1, hv1post⟩ := spec_result (verify_spec H hH root n1 index d1 p1)
    simp only [hv1]
    cases v1 with
    | false => simp
    | true =>
      obtain ⟨v2, hv2, hv2post⟩ := spec_result (verify_spec H hH root n2 index d2 p2)
      simp only [hv2]
      cases v2 with
      | false => simp
      | true =>
        obtain ⟨r1, hr1, hs1⟩ := hv1post rfl
        obtain ⟨r2, hr2, hs2⟩ := hv2post rfl
        obtain ⟨o, ho, c, hc, hcoll⟩ := spec_result
          (extract_spec H hH root index n1 d1 p1 n2 d2 p2 he r1 r2 hr1 hr2 hs1 hs2)
        subst o
        simp [ho, hcoll]

end Binding

end examples.merkle
