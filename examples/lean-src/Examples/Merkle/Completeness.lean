module

public import Examples.Merkle.Lawful

/-! Completeness: the honest proof for every leaf verifies.

The proof models the tree over lists: `nextLevel` builds the level above a
level, `levelsFrom` lists every level from the leaves up, `topOf` is the top
level and `proofFrom` the siblings on a leaf's path. Each loop of the
extracted code gets a `@[step]` spec relating it to this model, and
`inner_root` recomputes the first node of the top level from the honest
proof by following `nextLevel` one level at a time.
-/

open Aeneas Aeneas.Std Result

namespace examples.merkle

namespace Completeness

/-! ## Pure model of the tree -/

section Model

variable {D : Type _}

/-- The level above `l`: adjacent pairs are hashed with `nd` and an odd last
node moves up unchanged. -/
def nextLevel (nd : D → D → D) : List D → List D
  | a :: b :: rest => nd a b :: nextLevel nd rest
  | l => l

theorem nextLevel_of_length_le (nd : D → D → D) (l : List D) (h : l.length ≤ 1) :
    nextLevel nd l = l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp at h

theorem nextLevel_length (nd : D → D → D) (l : List D) :
    (nextLevel nd l).length = l.length / 2 + l.length % 2 := by
  fun_induction nextLevel nd l
  · simp only [List.length_cons, *]; agrind
  · rename_i l h
    match l with
    | [] => simp
    | [_] => simp
    | _ :: _ :: _ => exact absurd rfl (h _ _ _)

theorem nextLevel_length_lt (nd : D → D → D) (l : List D) (h : 1 < l.length) :
    (nextLevel nd l).length < l.length := by
  rw [nextLevel_length]; agrind

/-- The levels from `l` up to the top, as `Tree::new` builds them. -/
def levelsFrom (nd : D → D → D) (l : List D) : List (List D) :=
  if 1 < l.length then l :: levelsFrom nd (nextLevel nd l) else [l]
termination_by l.length
decreasing_by exact nextLevel_length_lt nd l ‹_›

/-- The top level above `l`. -/
def topOf (nd : D → D → D) (l : List D) : List D :=
  if 1 < l.length then topOf nd (nextLevel nd l) else l
termination_by l.length
decreasing_by exact nextLevel_length_lt nd l ‹_›

/-- The sibling of the node at `i` on level `l`, if it has one. -/
def sib (l : List D) (i : Nat) : List D :=
  if i % 2 = 1 then l[i - 1]?.toList else l[i + 1]?.toList

/-- The siblings on the path of the node at `i` on level `l` up to the top. -/
def proofFrom (nd : D → D → D) (l : List D) (i : Nat) : List D :=
  if 1 < l.length then sib l i ++ proofFrom nd (nextLevel nd l) (i / 2) else []
termination_by l.length
decreasing_by exact nextLevel_length_lt nd l ‹_›

/-- Hashes `acc`, the node at `i`, with its sibling `s`. -/
def stepF (nd : D → D → D) (i : Nat) (acc s : D) : D :=
  if i % 2 = 1 then nd s acc else nd acc s

theorem sib_cons_cons (x y : D) (rest : List D) (j : Nat) :
    sib (x :: y :: rest) (j + 2) = sib rest j := by
  rcases j with _ | j
  · simp [sib]
  · simp only [sib]
    have h1 : (j + 1 + 2) % 2 = (j + 1) % 2 := by agrind
    rw [h1]
    split
    · simp
    · simp

theorem nextLevel_getElem?_sib (nd : D → D → D) (l : List D) (i : Nat) (a s : D)
    (ha : l[i]? = some a) (hs : sib l i = [s]) :
    (nextLevel nd l)[i / 2]? = some (stepF nd i a s) := by
  fun_induction nextLevel nd l generalizing i
  · rename_i x y rest ih
    match i with
    | 0 => simp_all [sib, stepF]
    | 1 => simp_all [sib, stepF]
    | j + 2 =>
      rw [sib_cons_cons] at hs
      have := ih j (by simpa using ha) hs
      have h1 : (j + 2) / 2 = j / 2 + 1 := by agrind
      have h2 : stepF nd (j + 2) a s = stepF nd j a s := by simp [stepF]
      simp [h1, h2, this]
  · rename_i l h
    match l, i with
    | [], _ => simp at ha
    | [_], 0 => simp [sib] at hs
    | [_], _ + 1 => simp at ha
    | _ :: _ :: _, _ => exact absurd rfl (h _ _ _)

theorem nextLevel_getElem?_nil (nd : D → D → D) (l : List D) (i : Nat) (a : D)
    (ha : l[i]? = some a) (hs : sib l i = []) :
    (nextLevel nd l)[i / 2]? = some a := by
  fun_induction nextLevel nd l generalizing i
  · rename_i x y rest ih
    match i with
    | 0 => simp_all [sib]
    | 1 => simp_all [sib]
    | j + 2 =>
      rw [sib_cons_cons] at hs
      have := ih j (by simpa using ha) hs
      have h1 : (j + 2) / 2 = j / 2 + 1 := by agrind
      simp [h1, this]
  · rename_i l h
    match l, i with
    | [], _ => simp at ha
    | [_], 0 => simpa using ha
    | [_], _ + 1 => simp at ha
    | _ :: _ :: _, _ => exact absurd rfl (h _ _ _)

theorem sib_cases (l : List D) (i : Nat) : sib l i = [] ∨ ∃ s, sib l i = [s] := by
  unfold sib
  split
  · cases l[i - 1]?
    · simp
    · simp
  · cases l[i + 1]?
    · simp
    · simp

theorem levelsFrom_of_lt (nd : D → D → D) (l : List D) (h : 1 < l.length) :
    levelsFrom nd l = l :: levelsFrom nd (nextLevel nd l) := by
  rw [levelsFrom]; simp [h]

theorem levelsFrom_of_not_lt (nd : D → D → D) (l : List D) (h : ¬ 1 < l.length) :
    levelsFrom nd l = [l] := by
  rw [levelsFrom]; simp [h]

theorem topOf_of_lt (nd : D → D → D) (l : List D) (h : 1 < l.length) :
    topOf nd l = topOf nd (nextLevel nd l) := by
  rw [topOf]; simp [h]

theorem topOf_of_not_lt (nd : D → D → D) (l : List D) (h : ¬ 1 < l.length) :
    topOf nd l = l := by
  rw [topOf]; simp [h]

theorem proofFrom_of_lt (nd : D → D → D) (l : List D) (i : Nat) (h : 1 < l.length) :
    proofFrom nd l i = sib l i ++ proofFrom nd (nextLevel nd l) (i / 2) := by
  rw [proofFrom]; simp [h]

theorem proofFrom_of_not_lt (nd : D → D → D) (l : List D) (i : Nat) (h : ¬ 1 < l.length) :
    proofFrom nd l i = [] := by
  rw [proofFrom]; simp [h]

theorem levelsFrom_length_pos (nd : D → D → D) (l : List D) :
    0 < (levelsFrom nd l).length := by
  rw [levelsFrom]; split
  · simp
  · simp

theorem levelsFrom_getElem?_zero (nd : D → D → D) (l : List D) :
    (levelsFrom nd l)[0]? = some l := by
  rw [levelsFrom]; split
  · simp
  · simp

theorem levelsFrom_getElem?_last (nd : D → D → D) (l : List D) :
    (levelsFrom nd l)[(levelsFrom nd l).length - 1]? = some (topOf nd l) := by
  fun_induction levelsFrom nd l
  · rename_i l h ih
    rw [topOf_of_lt nd l h, ← ih]
    have := levelsFrom_length_pos nd (nextLevel nd l)
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [List.getElem?_cons]
    split
    · agrind
    · rfl
  · rename_i l h
    simp [topOf_of_not_lt nd l h]

theorem topOf_ne_nil (nd : D → D → D) (l : List D) (h : l ≠ []) : topOf nd l ≠ [] := by
  fun_induction topOf nd l
  · rename_i l hl ih
    apply ih
    have := nextLevel_length nd l
    rw [← List.length_pos_iff] at h ⊢
    agrind
  · assumption

end Model

/-! ## Lawful hash functions as pure functions -/

section Hash

variable {Hs D : Type _} {H : Hash Hs D}

/-- `H.leaf` as a pure function. -/
noncomputable def leafF (hH : H.Lawful) (s : Slice Std.U8) : D := Classical.choose (hH.leaf_ok s)

/-- `H.node` as a pure function. -/
noncomputable def nodeF (hH : H.Lawful) (a b : D) : D := Classical.choose (hH.node_ok a b)

/-- `H.size` as a pure function. -/
noncomputable def sizeF (hH : H.Lawful) (a : D) (n : Std.Usize) : D :=
  Classical.choose (hH.size_ok a n)

@[step]
theorem leaf.spec (hH : H.Lawful) (s : Slice Std.U8) :
    H.leaf s ⦃ (d : D) => d = leafF hH s ⦄ := by
  rw [Classical.choose_spec (hH.leaf_ok s)]; simp [leafF]

@[step]
theorem node.spec (hH : H.Lawful) (a b : D) :
    H.node a b ⦃ (d : D) => d = nodeF hH a b ⦄ := by
  rw [Classical.choose_spec (hH.node_ok a b)]; simp [nodeF]

@[step]
theorem size.spec (hH : H.Lawful) (a : D) (n : Std.Usize) :
    H.size a n ⦃ (d : D) => d = sizeF hH a n ⦄ := by
  rw [Classical.choose_spec (hH.size_ok a n)]; simp [sizeF]

@[step]
theorem eq.spec (hH : H.Lawful) (a b : D) :
    H.corecmpEqInst.partialEqInst.eq a b ⦃ (r : Bool) => (r = true ↔ a = b) ⦄ := by
  rw [hH.eq_ok]; simp

end Hash

/-! ## Specs of the extracted functions -/

section Impl

variable {Hs D : Type _} {H : Hash Hs D}

/-- `Usize.max` is odd, so an even index below it is at most `Usize.max - 1`. -/
theorem usize_max_odd : Usize.max % 2 = 1 := by
  rcases Usize.bounds_eq with h | h
  · rw [h]; scalar_tac
  · rw [h]; scalar_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 0)**: hashes the remaining data into leaves. -/
@[step]
theorem Tree.new_loop0.spec (hH : H.Lawful) (data : Slice (alloc.vec.Vec Std.U8))
    (level : alloc.vec.Vec D) (i : Std.Usize)
    (hi : i.val ≤ data.length) (hlevel : level.length = i.val) :
    Tree.new_loop0 H data level i ⦃ (res : alloc.vec.Vec D) =>
      res.val = level.val ++ (data.val.drop i.val).map (fun v => leafF hH v.deref) ⦄ := by
  unfold Tree.new_loop0
  step*
  · agrind
  · rw [res_post, level1_post, i2_post, t_post, v_post,
      List.drop_eq_getElem_cons (by scalar_tac : i.val < data.val.length)]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
  · rw [List.drop_eq_nil_of_le (by scalar_tac : data.val.length ≤ i.val)]
    simp
termination_by data.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 2)**: hashes the
remaining adjacent pairs of `level` into `next`. -/
@[step]
theorem Tree.new_loop1_loop0.spec (hH : H.Lawful) (level next : alloc.vec.Vec D) (i : Std.Usize)
    (hi : i.val ≤ level.length) (heven : i.val % 2 = 0) (hnext : next.length ≤ i.val) :
    Tree.new_loop1_loop0 H level next i ⦃ (next' : alloc.vec.Vec D) (j : Std.Usize) =>
      next'.val ++ level.val.drop j.val = next.val ++ nextLevel (nodeF hH) (level.val.drop i.val) ∧
      j.val ≤ level.length ∧ level.length ≤ j.val + 1 ⦄ := by
  have := usize_max_odd
  unfold Tree.new_loop1_loop0
  step*
  · agrind
  · have e : level.val.drop i.val = t :: t1 :: level.val.drop (i.val + 2) := by
      rw [List.drop_eq_getElem_cons (by scalar_tac), List.drop_eq_getElem_cons (by scalar_tac)]
      simp [t_post, t1_post, i1_post]
    refine ⟨?_, next'_post1, next'_post2⟩
    rw [next'_post, next1_post, t2_post, i3_post, e]
    simp [nextLevel]
  · refine ⟨?_, by scalar_tac, by scalar_tac⟩
    rw [nextLevel_of_length_le _ _ (by simp; scalar_tac)]
termination_by level.length - i.val
decreasing_by scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::new` (loop 1)**: pushes
`level` and every level above it except the top onto `levels`, and returns
the top level. -/
@[step]
theorem Tree.new_loop1.spec (hH : H.Lawful) (level : alloc.vec.Vec D)
    (levels : alloc.vec.Vec (alloc.vec.Vec D))
    (hpos : 0 < level.length) (hsum : levels.length + level.length ≤ Usize.max) :
    Tree.new_loop1 H level levels ⦃ (top : alloc.vec.Vec D)
        (lvls : alloc.vec.Vec (alloc.vec.Vec D)) =>
      lvls.val.map alloc.vec.Vec.val ++ [top.val] =
        levels.val.map alloc.vec.Vec.val ++ levelsFrom (nodeF hH) level.val ∧
      lvls.length < Usize.max ⦄ := by
  have hnl := nextLevel_length (nodeF hH) level.val
  unfold Tree.new_loop1
  dsimp only
  split
  · step as ⟨next, i1, hnext, hi1, hi1'⟩
    simp only [List.drop_zero, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at hnext
    have hlen := congrArg List.length hnext
    simp only [List.length_append, List.length_drop] at hlen
    split
    · step as ⟨x, hx⟩
      step as ⟨next1, hnext1⟩
      have hd : level.val.drop i1.val = [x] := by
        rw [List.drop_eq_getElem_cons (by scalar_tac), List.drop_eq_nil_of_le (by scalar_tac)]
        simp [hx]
      have hn1 : next1.val = nextLevel (nodeF hH) level.val := by
        rw [hnext1, ← hnext, hd]
      have hlt : next1.length < level.length := by
        simp only [alloc.vec.Vec.length, hn1, hnl]; agrind
      step*
      · agrind
      · refine ⟨?_, ‹_›⟩
        rw [top_post, levels1_post, hn1, levelsFrom_of_lt _ level.val (by scalar_tac)]
        simp
    · have hd : level.val.drop i1.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      have hn1 : next.val = nextLevel (nodeF hH) level.val := by
        rw [← hnext, hd, List.append_nil]
      have hlt : next.length < level.length := by
        simp only [alloc.vec.Vec.length, hn1, hnl]; agrind
      step*
      · agrind
      · refine ⟨?_, ‹_›⟩
        rw [top_post, levels1_post, hn1, levelsFrom_of_lt _ level.val (by scalar_tac)]
        simp
  · simp [WP.uncurry', levelsFrom_of_not_lt _ _ (by scalar_tac : ¬ 1 < level.val.length)]
    scalar_tac
termination_by level.length
decreasing_by
  · agrind
  · agrind

/-- **Spec theorem for `examples::merkle::Tree::new`**: the levels are the leaf
hashes and every level above them. -/
@[step]
theorem Tree.new.spec (hH : H.Lawful) (data : Slice (alloc.vec.Vec Std.U8))
    (hpos : 0 < data.length) :
    Tree.new H data ⦃ (tree : Tree Hs D) =>
      tree.levels.val.map alloc.vec.Vec.val =
        levelsFrom (nodeF hH) (data.val.map (fun v => leafF hH v.deref)) ⦄ := by
  unfold Tree.new
  step*
  · simp only [List.drop_zero, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append,
      List.map_nil] at level_post level1_post
    rw [levels1_post, List.map_append, List.map_cons, List.map_nil, level1_post, level_post]

theorem map_val_getElem? {α : Type _} (L : List (alloc.vec.Vec α)) (M : List (List α))
    (hL : L.map alloc.vec.Vec.val = M) (k : Nat) (hk : k < L.length) :
    M[k]? = some L[k].val := by
  subst hL; simp [hk]

theorem map_val_getElem_eq {α : Type _} (L : List (alloc.vec.Vec α)) (M : List (List α))
    (hL : L.map alloc.vec.Vec.val = M) (k : Nat) (hk : k < L.length) (x : List α)
    (hx : M[k]? = some x) : L[k].val = x := by
  subst hL; simpa [hk] using hx

theorem getElem?_of_val_eq {α : Type _} (l : List α) (v : alloc.vec.Vec α) (hv : v.val = l)
    (j : Std.Usize) (n : Nat) (hj : j.val = n) (h : j.val < v.val.length) :
    l[n]? = some v.val[j.val] := by
  subst hv hj; simp [h]

theorem map_val_length {α : Type _} (L : List (alloc.vec.Vec α)) (M : List (List α))
    (hL : L.map alloc.vec.Vec.val = M) : L.length = M.length := by
  subst hL; simp

/-- **Spec theorem for `examples::merkle::Tree::root`**: the size commitment of
the first node of the top level. -/
@[step]
theorem Tree.root.spec (hH : H.Lawful) (self : Tree Hs D) (l : List D)
    (hL : self.levels.val.map alloc.vec.Vec.val = levelsFrom (nodeF hH) l) (hpos : 0 < l.length) :
    Tree.root H self ⦃ (r : Option D) =>
      ∃ t m, (topOf (nodeF hH) l).head? = some t ∧ m.val = l.length ∧ r = some (sizeF hH t m) ⦄ := by
  have hlen := map_val_length _ _ hL
  have hpos' := levelsFrom_length_pos (nodeF hH) l
  have hne := topOf_ne_nil (nodeF hH) l (List.ne_nil_of_length_pos hpos)
  unfold Tree.root Tree.size
  step*
  · have htop : top.val = topOf (nodeF hH) l := by
      rw [top_post]; apply map_val_getElem_eq _ _ hL
      rw [show i1.val = (levelsFrom (nodeF hH) l).length - 1 by scalar_tac]
      exact levelsFrom_getElem?_last _ _
    rw [← htop] at hne
    rw [‹b = true›] at b_post
    exact absurd (by simpa using b_post) hne
  · have htop : top.val = topOf (nodeF hH) l := by
      rw [top_post]; apply map_val_getElem_eq _ _ hL
      rw [show i1.val = (levelsFrom (nodeF hH) l).length - 1 by scalar_tac]
      exact levelsFrom_getElem?_last _ _
    have hx : x.val = l := by
      rw [x_post]; exact map_val_getElem_eq _ _ hL 0 _ l (levelsFrom_getElem?_zero _ _)
    refine ⟨t, x.len, ?_, by simp [hx], by rw [t1_post]⟩
    rw [← htop, t_post]; simp [List.head?_eq_getElem?]

/-- **Spec theorem for `examples::merkle::Tree::proof` (loop)**: appends the
siblings on the path of the node at `index` on level `k`. -/
@[step]
theorem Tree.proof_loop.spec (hH : H.Lawful) (self : Tree Hs D) (proof : alloc.vec.Vec D)
    (index k : Std.Usize) (l : List D)
    (hL : (self.levels.val.map alloc.vec.Vec.val).drop k.val = levelsFrom (nodeF hH) l)
    (hidx : index.val < l.length) (hp : proof.length ≤ k.val) :
    Tree.proof_loop self proof index k ⦃ (res : alloc.vec.Vec D) =>
      res.val = proof.val ++ proofFrom (nodeF hH) l index.val ⦄ := by
  have hlen := congrArg List.length hL
  simp only [List.length_drop, List.length_map] at hlen
  unfold Tree.proof_loop
  by_cases hl : 1 < l.length
  · have hdrop : (self.levels.val.map alloc.vec.Vec.val).drop k.val =
        l :: levelsFrom (nodeF hH) (nextLevel (nodeF hH) l) := by
      rw [hL, levelsFrom_of_lt _ _ hl]
    have hpos := levelsFrom_length_pos (nodeF hH) (nextLevel (nodeF hH) l)
    rw [levelsFrom_of_lt _ _ hl] at hlen
    have hlev : ∀ (h : k.val < self.levels.length), (self.levels.val[k.val]).val = l := by
      intro h
      have h2 := congrArg (fun L => L[0]?) hdrop
      simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_map, List.getElem?_cons_zero] at h2
      rw [List.getElem?_eq_getElem h] at h2
      simpa using h2
    have hk : k.val + 1 < self.levels.length := by
      simp only [List.length_cons] at hlen; agrind
    step as ⟨i, hi⟩
    have hL' : (self.levels.val.map alloc.vec.Vec.val).drop i.val =
        levelsFrom (nodeF hH) (nextLevel (nodeF hH) l) := by
      rw [hi, ← List.drop_drop, hdrop]; rfl
    have hidx' : index.val / 2 < (nextLevel (nodeF hH) l).length := by
      rw [nextLevel_length]; agrind
    step*
    have hlevel : level.val = l := by rw [level_post]; exact hlev _
    split
    · step as ⟨j, hj⟩
      step as ⟨x, hx⟩
      have hs : sib l index.val = [x] := by
        simp only [sib, show index.val % 2 = 1 by scalar_tac, ↓reduceIte]
        rw [getElem?_of_val_eq l level hlevel j _ (by agrind) (by agrind), hx]
        rfl
      step*
      · agrind
      · rw [res_post, proofFrom_of_lt _ _ _ hl, hs, proof1_post, index1_post]
        simp
    · step as ⟨j, hj⟩
      split
      · step as ⟨x, hx⟩
        have hs : sib l index.val = [x] := by
          simp only [sib, show ¬ index.val % 2 = 1 by scalar_tac, ↓reduceIte]
          rw [getElem?_of_val_eq l level hlevel j _ (by agrind) (by agrind), hx]
          rfl
        step*
        · agrind
        · rw [res_post, proofFrom_of_lt _ _ _ hl, hs, proof1_post, index1_post]
          simp
      · have hs : sib l index.val = [] := by
          simp only [sib, show ¬ index.val % 2 = 1 by scalar_tac, ↓reduceIte]
          rw [List.getElem?_eq_none (by scalar_tac)]
          rfl
        step*
        rw [res_post, proofFrom_of_lt _ _ _ hl, hs, index1_post]
        simp
  · rw [levelsFrom_of_not_lt _ _ hl] at hlen
    simp only [List.length_cons] at hlen
    have : k.val < self.levels.length := by agrind
    step*
    simp [proofFrom_of_not_lt _ _ _ hl]
termination_by self.levels.length - k.val
decreasing_by
  · scalar_decr_tac
  · scalar_decr_tac
  · scalar_decr_tac

/-- **Spec theorem for `examples::merkle::Tree::proof`**: the siblings on the
path of leaf `index`. -/
@[step]
theorem Tree.proof.spec (hH : H.Lawful) (self : Tree Hs D) (l : List D)
    (hL : self.levels.val.map alloc.vec.Vec.val = levelsFrom (nodeF hH) l) (index : Std.Usize)
    (hidx : index.val < l.length) :
    Tree.proof H self index ⦃ (r : Option (alloc.vec.Vec D)) =>
      ∃ p, r = some p ∧ p.val = proofFrom (nodeF hH) l index.val ⦄ := by
  have hlen := map_val_length _ _ hL
  have hpos := levelsFrom_length_pos (nodeF hH) l
  have hL0 : (self.levels.val.map alloc.vec.Vec.val).drop (0#usize).val = levelsFrom (nodeF hH) l := by
    simpa using hL
  unfold Tree.proof Tree.size
  step*
  have hx : x.val = l := by
    rw [x_post]; exact map_val_getElem_eq _ _ hL 0 _ l (levelsFrom_getElem?_zero _ _)
  scalar_tac

/-- **Spec theorem for `examples::merkle::has_sibling`** -/
@[step]
theorem has_sibling.spec (index width : Std.Usize) (h : index.val < width.val) :
    has_sibling index width ⦃ (b : Bool) =>
      (b = true ↔ (index.val % 2 = 1 ∨ index.val + 1 < width.val)) ⦄ := by
  unfold has_sibling
  step*

/-- **Spec theorem for `examples::merkle::step`** -/
@[step]
theorem merkle_step.spec (hH : H.Lawful) (index : Std.Usize) (acc s : D) :
    merkle.step H index acc s ⦃ (r : D) => r = stepF (nodeF hH) index.val acc s ⦄ := by
  unfold merkle.step
  step*
  · simp only [r_post, stepF, show index.val % 2 = 1 by scalar_tac, ↓reduceIte]
  · simp only [r_post, stepF, show ¬ index.val % 2 = 1 by scalar_tac, ↓reduceIte]

/-- **Spec theorem for `examples::merkle::parent_width`** -/
@[step]
theorem parent_width.spec (width : Std.Usize) :
    parent_width width ⦃ (r : Std.Usize) => r.val = width.val / 2 + width.val % 2 ⦄ := by
  unfold parent_width
  step*

theorem eq_ok_of_spec {m : Result Bool} (h : m ⦃ (b : Bool) => b = true ⦄) : m = ok true := by
  cases m
  · simpa using h
  · simp at h
  · simp at h

/-- **Spec theorem for `examples::merkle::inner_root` (loop)**: given the node
`acc` at `index` on level `l` and the rest of the honest proof, recomputes
the first node of the top level. -/
@[step]
theorem inner_root_loop.spec (hH : H.Lawful) (proof : Slice D) (acc : D)
    (index width i : Std.Usize) (l : List D)
    (hw : width.val = l.length) (hacc : l[index.val]? = some acc)
    (hp : proof.val.drop i.val = proofFrom (nodeF hH) l index.val) (hi : i.val ≤ proof.length) :
    inner_root_loop H proof acc index width i ⦃ (r : Option D) =>
      r = (topOf (nodeF hH) l).head? ⦄ := by
  have hidx : index.val < l.length := (List.getElem?_eq_some_iff.mp hacc).1
  unfold inner_root_loop
  by_cases hl : 1 < l.length
  · have hp' : proof.val.drop i.val =
        sib l index.val ++ proofFrom (nodeF hH) (nextLevel (nodeF hH) l) (index.val / 2) := by
      rw [hp, proofFrom_of_lt _ _ _ hl]
    have hw' : (nextLevel (nodeF hH) l).length = width.val / 2 + width.val % 2 := by
      rw [nextLevel_length, hw]
    rw [topOf_of_lt _ _ hl]
    simp only [show width > 1#usize by scalar_tac, ↓reduceIte]
    step as ⟨b, hb⟩
    split
    · obtain hs | ⟨s, hs⟩ := sib_cases l index.val
      · exfalso
        have hb' := hb.mp ‹_›
        simp only [sib] at hs
        split at hs
        · rw [List.getElem?_eq_getElem (by agrind)] at hs
          simp at hs
        · rw [List.getElem?_eq_getElem (by agrind)] at hs
          simp at hs
      · have hlt : i.val < proof.length := by
          by_contra hc
          rw [List.drop_eq_nil_of_le (by scalar_tac), hs] at hp'
          simp at hp'
        have hpi : proof.val[i.val] = s := by
          have h2 := congrArg (·[0]?) hp'
          simp only [List.getElem?_drop, Nat.add_zero, hs, List.cons_append,
            List.getElem?_cons_zero, List.getElem?_eq_getElem hlt] at h2
          simpa using h2
        have hrest : proof.val.drop (i.val + 1) =
            proofFrom (nodeF hH) (nextLevel (nodeF hH) l) (index.val / 2) := by
          rw [← List.drop_drop, hp', hs]; rfl
        have hacc' := nextLevel_getElem?_sib (nodeF hH) l index.val acc s hacc hs
        simp only [show ¬ (i ≥ proof.len) by scalar_tac, ↓reduceIte]
        step as ⟨t, ht⟩
        step as ⟨acc1, hacc1⟩
        step as ⟨i2, hi2⟩
        step as ⟨index1, hindex1⟩
        step as ⟨width1, hwidth1⟩
        step with inner_root_loop.spec hH proof acc1 index1 width1 i2 (nextLevel (nodeF hH) l)
        exact r_post
    · have hs : sib l index.val = [] := by
        have hb' : ¬ (index.val % 2 = 1 ∨ index.val + 1 < width.val) :=
          fun h => ‹¬ b = true› (hb.mpr h)
        simp only [sib, show ¬ index.val % 2 = 1 by agrind, ↓reduceIte]
        rw [List.getElem?_eq_none (by agrind)]; rfl
      have hacc' := nextLevel_getElem?_nil (nodeF hH) l index.val acc hacc hs
      rw [hs, List.nil_append] at hp'
      step as ⟨index1, hindex1⟩
      step as ⟨width1, hwidth1⟩
      step with inner_root_loop.spec hH proof acc index1 width1 i (nextLevel (nodeF hH) l)
      exact r_post
  · have hi0 : index.val = 0 := by agrind
    have hpn : proof.val.drop i.val = [] := by rw [hp, proofFrom_of_not_lt _ _ _ hl]
    have hieq : i.val = proof.length := by
      have := List.drop_eq_nil_iff.mp hpn; agrind
    rw [topOf_of_not_lt _ _ hl]
    simp only [show ¬ width > 1#usize by scalar_tac, ↓reduceIte]
    step*
    simp [List.head?_eq_getElem?, ← hi0, hacc]
termination_by width.val
decreasing_by
  · scalar_decr_tac
  · scalar_decr_tac

/-- **Spec theorem for `examples::merkle::inner_root`**: with the honest proof
for leaf `index`, recomputes the first node of the top level. -/
@[step]
theorem inner_root.spec (hH : H.Lawful) (size index : Std.Usize) (data : Slice Std.U8)
    (proof : Slice D) (l : List D)
    (hsize : size.val = l.length) (hleaf : l[index.val]? = some (leafF hH data))
    (hp : proof.val = proofFrom (nodeF hH) l index.val) :
    inner_root H size index data proof ⦃ (r : Option D) => r = (topOf (nodeF hH) l).head? ⦄ := by
  have hidx : index.val < l.length := (List.getElem?_eq_some_iff.mp hleaf).1
  unfold inner_root
  simp only [show ¬ index ≥ size by scalar_tac, ↓reduceIte]
  step as ⟨acc, hacc⟩
  step with inner_root_loop.spec hH proof acc index size 0#usize l
  · simpa using hp
  · exact r_post

/-- **Spec theorem for `examples::merkle::verify`**: the honest proof verifies
against the honest root. -/
@[step]
theorem verify.spec (hH : H.Lawful) (root : D) (size index : Std.Usize) (data : Slice Std.U8)
    (proof : Slice D) (l : List D) (t : D)
    (hsize : size.val = l.length) (hleaf : l[index.val]? = some (leafF hH data))
    (hp : proof.val = proofFrom (nodeF hH) l index.val)
    (ht : (topOf (nodeF hH) l).head? = some t) (hroot : root = sizeF hH t size) :
    verify H root size index data proof ⦃ (b : Bool) => b = true ⦄ := by
  unfold verify
  step with inner_root.spec hH size index data proof l hsize hleaf hp as ⟨o, ho⟩
  rw [ho, ht]
  step*

/-- **Spec theorem for `examples::merkle::completeness`** -/
theorem completeness.spec (hH : H.Lawful) (data : Slice (alloc.vec.Vec Std.U8))
    (index : Std.Usize) :
    completeness H data index ⦃ (b : Bool) => b = true ⦄ := by
  unfold completeness
  dsimp only
  split
  · simp
  · have hpos : 0 < data.length := by scalar_tac
    step with Tree.new.spec hH data hpos as ⟨tree, hL⟩
    step with Tree.root.spec hH tree _ hL (by simpa using hpos) as ⟨o, t, m, ht, hm, ho⟩
    subst ho
    step with Tree.proof.spec hH tree _ hL index (by simp; scalar_tac) as ⟨o1, p, ho1, hp⟩
    subst ho1
    step*
    · rw [List.getElem?_map, List.getElem?_eq_getElem (by scalar_tac), v_post]; rfl
    · simp [alloc.vec.Vec.deref, hp]
    · have : m = data.len := by scalar_tac
      rw [this]

end Impl

/-- Completeness: for every lawful `H`, the honest proof for every leaf
verifies against the honest root. -/
public theorem completeness_spec {Hs D : Type _} (H : Hash Hs D) (hH : H.Lawful)
    (data : Slice (alloc.vec.Vec Std.U8)) (index : Std.Usize) :
    completeness H data index = ok true :=
  eq_ok_of_spec (completeness.spec hH data index)

end Completeness

end examples.merkle


