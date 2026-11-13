/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import Mathlib.Algebra.Group.Action.Basic

/-!
# The Serre graph of a parent map

A map `p : V → V` defines a Serre graph on `V` with one geometric edge joining each vertex `v` to
its parent `p v`. A reduced path from `a` to `b` in this graph has length `k + l` for some `k` and
`l` with `p^[k] a = p^[l] b`, and when `k` and `l` are both positive the vertices `p^[k - 1] a`
and `p^[l - 1] b` just below this common iterated parent are distinct. Hence the graph is a forest
as soon as no vertex is a proper iterated parent of itself, and a nonempty such graph is a tree
when moreover any two vertices have a common iterated parent. Under the first hypothesis the
iterated parents of a vertex are pairwise distinct, so these trees are infinite. Examples are the
line, with parent map `n ↦ n + 1` on the integers, and the tree attached by Serre to an
increasing union of subgroups.

A group acting on `V` and commuting with the parent map acts on the graph by automorphisms that
preserve the orientation of every edge towards the parent.

## Main declarations

* `TauCeti.SerreGraph.ofParent`: the Serre graph of a parent map.
* `TauCeti.SerreGraph.exists_iterate_eq_of_isReduced`: the length of a reduced path and the common
  iterated parent of its endpoints.
* `TauCeti.SerreGraph.ofParent_nonempty_path_iff`: two vertices are joined by a path exactly when
  they have a common iterated parent.
* `TauCeti.SerreGraph.ofParent_isAcyclic`, `TauCeti.SerreGraph.ofParent_preconnected_iff`,
  `TauCeti.SerreGraph.ofParent_isTree`: forests and trees among these graphs.
* `TauCeti.SerreGraph.ofParentAction`: the action of a group commuting with the parent map.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §6.1.
-/

public section

universe u w

namespace TauCeti
namespace SerreGraph

variable {V : Type u} (p : V → V)

/-- The Serre graph of a parent map `p : V → V`: its vertices are the elements of `V`, and each
vertex `v` carries a dart `(v, true)` from `v` to its parent `p v` and the reverse dart
`(v, false)` from `p v` to `v`. The definition unfolds at instance transparency, so that an
element of `V` or of `V × Bool` is accepted as a vertex or a dart by rewriting and
simplification. -/
@[expose, instance_reducible] def ofParent : SerreGraph.{u, u} where
  V := V
  E := V × Bool
  src e := if e.2 then e.1 else p e.1
  rev e := (e.1, !e.2)
  rev_rev e := by simp
  rev_ne e := by simp [Prod.ext_iff]

@[simp] theorem ofParent_src_true (v : V) : (ofParent p).src (v, true) = v := rfl

@[simp] theorem ofParent_src_false (v : V) : (ofParent p).src (v, false) = p v := rfl

@[simp] theorem ofParent_tgt_true (v : V) : (ofParent p).tgt (v, true) = p v := rfl

@[simp] theorem ofParent_tgt_false (v : V) : (ofParent p).tgt (v, false) = v := rfl

@[simp] theorem ofParent_rev (e : V × Bool) : (ofParent p).rev e = (e.1, !e.2) := rfl

/-! ### Reduced paths -/

/-- Every vertex is joined to each of its iterated parents. -/
theorem ofParent_nonempty_path_iterate (v : V) (n : ℕ) :
    Nonempty ((ofParent p).Path v (p^[n] v)) := by
  induction n with
  | zero => exact ⟨.nil⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.some.cons ⟨(p^[n] v, true), rfl, rfl⟩⟩

/-- The parent map, as a map on the vertices of its graph. The arrows of the quiver of
`ofParent p` join elements of `(ofParent p).V`, and `p v` has type `V`, so the darts below are
stated between `v` and `parent p v`. Its iterates are converted back by `parent_iterate`. -/
private def parent (v : (ofParent p).V) : (ofParent p).V := p v

private theorem parent_iterate (k : ℕ) (v : (ofParent p).V) : (parent p)^[k] v = p^[k] v := rfl

/-- The invariant of a reduced path `q` from `a` to `b`: its length is `k + l`, where the
iterated parents `parent^[k] a` and `parent^[l] b` agree and the vertices `parent^[k - 1] a` and
`parent^[l - 1] b` differ when `k` and `l` are positive; moreover a dart towards a parent extends
`q` to a reduced path only if `l = 0`, and a dart away from a parent that does so ends at a
vertex other than `parent^[k - 1] a` when `l = 0` and `0 < k`. -/
private def IsClimbDescent {a b : (ofParent p).V} (q : (ofParent p).Path a b) (k l : ℕ) : Prop :=
  k + l = q.length ∧ (parent p)^[k] a = (parent p)^[l] b ∧
    (0 < k → 0 < l → (parent p)^[k - 1] a ≠ (parent p)^[l - 1] b) ∧
    ∀ {c : (ofParent p).V} (e : Quiver.Hom b c), Path.IsReduced (ofParent p) (q.cons e) →
      if e.1.2 then l = 0 else l = 0 → 0 < k → (parent p)^[k - 1] a ≠ c

variable {p} in
/-- Extending a reduced path by a dart away from a parent increases `l`. -/
private theorem IsClimbDescent.cons_false {a c : (ofParent p).V}
    {q : (ofParent p).Path a (parent p c)} {k l : ℕ} (h : IsClimbDescent p q k l)
    (hq : Path.IsReduced (ofParent p)
      (q.cons (⟨(c, false), rfl, rfl⟩ : Quiver.Hom (parent p c) c))) :
    IsClimbDescent p (q.cons (⟨(c, false), rfl, rfl⟩ : Quiver.Hom (parent p c) c)) k (l + 1) := by
  obtain ⟨hkl, heq, hne, hext⟩ := h
  have hf := hext _ hq
  refine ⟨by rw [Quiver.Path.length_cons]; omega, by rw [heq, Function.iterate_succ_apply],
    fun hk _ => ?_, fun e he => ?_⟩
  · rw [Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · exact hf rfl hk
    · rw [← Nat.sub_add_cancel hl, Function.iterate_succ_apply]
      exact hne hk hl
  · -- A dart towards the parent of `c` would reverse the last dart.
    obtain ⟨⟨x, d⟩, hs, ht⟩ := e
    cases d
    · simp
    · obtain rfl : x = c := hs
      exact absurd rfl ((Path.isReduced_cons_cons _ _ _ _).mp he).2

variable {p} in
/-- A reduced path can only be extended by a dart towards a parent if `l = 0`, and then `k`
increases. -/
private theorem IsClimbDescent.cons_true {a b : (ofParent p).V} {q : (ofParent p).Path a b}
    {k l : ℕ} (h : IsClimbDescent p q k l)
    (hq : Path.IsReduced (ofParent p)
      (q.cons (⟨(b, true), rfl, rfl⟩ : Quiver.Hom b (parent p b)))) :
    IsClimbDescent p (q.cons (⟨(b, true), rfl, rfl⟩ : Quiver.Hom b (parent p b))) (k + 1) 0 := by
  obtain ⟨hkl, heq, -, hext⟩ := h
  obtain rfl : l = 0 := hext _ hq
  refine ⟨by rw [Quiver.Path.length_cons]; omega, by
      rw [Function.iterate_succ_apply', heq, Function.iterate_zero_apply,
        Function.iterate_zero_apply],
    by simp, fun e he => ?_⟩
  -- A dart away from the parent of `b` does not return to `b`.
  obtain ⟨⟨x, d⟩, hs, ht⟩ := e
  cases d
  · have hx : (x, false) ≠ (b, false) := ((Path.isReduced_cons_cons _ _ _ _).mp he).2
    obtain rfl : x = _ := ht
    intro _ _ h
    exact hx (Prod.ext (by rw [← h, Nat.add_sub_cancel, heq, Function.iterate_zero_apply]) rfl)
  · simp

/-- Every reduced path satisfies the invariant `IsClimbDescent`. -/
private theorem exists_isClimbDescent {a b : (ofParent p).V} (q : (ofParent p).Path a b)
    (hq : Path.IsReduced (ofParent p) q) : ∃ k l, IsClimbDescent p q k l := by
  induction q with
  | nil => exact ⟨0, 0, rfl, rfl, by simp, fun e _ => by split <;> simp⟩
  | @cons b c q f ih =>
    obtain ⟨k, l, h⟩ := ih (hq.of_cons _)
    obtain ⟨⟨w, d⟩, hs, ht⟩ := f
    cases d
    · obtain rfl : c = w := ht.symm
      obtain rfl : b = parent p c := hs.symm
      exact ⟨k, l + 1, IsClimbDescent.cons_false h hq⟩
    · obtain rfl : b = w := hs.symm
      obtain rfl : c = parent p b := ht.symm
      exact ⟨k + 1, 0, IsClimbDescent.cons_true h hq⟩

/-- A reduced path from `a` to `b` in the graph of a parent map has length `k + l`, where
`p^[k] a = p^[l] b`, and when `k` and `l` are both positive the two vertices `p^[k - 1] a` and
`p^[l - 1] b` just below this common iterated parent are distinct. -/
theorem exists_iterate_eq_of_isReduced {a b : V} (q : (ofParent p).Path a b)
    (hq : Path.IsReduced (ofParent p) q) :
    ∃ k l, k + l = q.length ∧ p^[k] a = p^[l] b ∧
      (0 < k → 0 < l → p^[k - 1] a ≠ p^[l - 1] b) := by
  obtain ⟨k, l, hkl, heq, hne, -⟩ := exists_isClimbDescent p q hq
  exact ⟨k, l, hkl, (parent_iterate p k a).symm.trans (heq.trans (parent_iterate p l b)),
    fun hk hl h => hne hk hl ((parent_iterate p _ a).trans (h.trans (parent_iterate p _ b).symm))⟩

/-! ### Forests and trees -/

/-- The graph of a parent map is a forest when no two distinct iterates of the parent map agree
at any vertex, that is, when no vertex is a proper iterated parent of itself. -/
theorem ofParent_isAcyclic (hp : ∀ v m n, p^[m] v = p^[n] v → m = n) :
    (ofParent p).IsAcyclic := by
  refine (isAcyclic_iff _).mpr fun a q hq => ?_
  obtain ⟨k, l, hkl, heq, hne⟩ := exists_iterate_eq_of_isReduced p q hq
  obtain rfl : k = l := hp a k l heq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Quiver.Path.eq_nil_of_length_zero _ hkl.symm
  · exact absurd rfl (hne hk hk)

/-- Two vertices of the graph of a parent map are joined by a path exactly when they have a
common iterated parent. -/
theorem ofParent_nonempty_path_iff {a b : V} :
    Nonempty ((ofParent p).Path a b) ↔ ∃ m n, p^[m] a = p^[n] b := by
  refine ⟨fun ⟨q⟩ => ?_, fun ⟨m, n, hmn⟩ => ?_⟩
  · obtain ⟨k, l, -, heq, -⟩ :=
      exists_iterate_eq_of_isReduced p _ (Path.isReduced_reduce (ofParent p) q)
    exact ⟨k, l, heq⟩
  · obtain ⟨q⟩ := ofParent_nonempty_path_iterate p a m
    obtain ⟨r⟩ := ofParent_nonempty_path_iterate p b n
    rw [hmn] at q
    exact ⟨q.comp r.reverse⟩

/-- The graph of a parent map is preconnected exactly when any two vertices have a common
iterated parent. -/
theorem ofParent_preconnected_iff :
    (ofParent p).Preconnected ↔ ∀ a b : V, ∃ m n, p^[m] a = p^[n] b :=
  (preconnected_iff _).trans (forall₂_congr fun _ _ => ofParent_nonempty_path_iff p)

/-- The graph of a parent map on a nonempty type is a tree when no vertex is a proper iterated
parent of itself and any two vertices have a common iterated parent. -/
theorem ofParent_isTree [Nonempty V] (hp : ∀ v m n, p^[m] v = p^[n] v → m = n)
    (h : ∀ a b : V, ∃ m n, p^[m] a = p^[n] b) : (ofParent p).IsTree :=
  (isTree_iff _).mpr
    ⟨(connected_iff _).mpr ⟨‹_›, (ofParent_preconnected_iff p).mpr h⟩, ofParent_isAcyclic p hp⟩

/-! ### Automorphisms -/

variable {G : Type w} [Group G] [MulAction G V]

/-- A group acting on the vertices and commuting with the parent map acts on the graph of the
parent map: an element carries the dart from `v` to its parent to the dart from `g • v` to its
parent. -/
def ofParentAction (h : ∀ (g : G) (v : V), p (g • v) = g • p v) : G →* (ofParent p).Aut where
  toFun g :=
    { equivV := (MulAction.toPerm g : Equiv.Perm V)
      equivE := (MulAction.toPerm g : Equiv.Perm V).prodCongr (Equiv.refl Bool)
      map_src e := by
        obtain ⟨v, d⟩ := e
        cases d
        exacts [h g v, rfl]
      map_rev _ := rfl }
  map_one' := Aut.ext (fun v : V => one_smul G v) fun e : V × Bool =>
    Prod.ext (one_smul G e.1) rfl
  map_mul' g g' := Aut.ext (fun v : V => mul_smul g g' v) fun e : V × Bool =>
    Prod.ext (mul_smul g g' e.1) rfl

variable {p}

@[simp] theorem ofParentAction_equivV (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (v : V) : (ofParentAction p h g).equivV v = g • v := (rfl)

@[simp] theorem ofParentAction_equivE (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (e : V × Bool) : (ofParentAction p h g).equivE e = (g • e.1, e.2) := (rfl)

/-- The automorphism attached to `g` moves a vertex `v` to `g • v`. -/
@[simp] theorem ofParentAction_smul_vertex (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (v : (ofParent p).V) : ofParentAction p h g • v = g • v := (rfl)

/-- The automorphism attached to `g` moves the dart `(v, b)` to `(g • v, b)`. -/
@[simp] theorem ofParentAction_smul_dart (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (e : (ofParent p).E) : ofParentAction p h g • e = (g • e.1, e.2) := (rfl)

/-- The action on the graph of a parent map has no inversions: it preserves the orientation of
each edge towards the parent. -/
theorem ofParentAction_equivE_ne_rev (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (e : V × Bool) : (ofParentAction p h g).equivE e ≠ (ofParent p).rev e := by
  rw [ofParentAction_equivE]
  exact fun h' => Bool.not_ne_self e.2 (congrArg Prod.snd h').symm

end SerreGraph
end TauCeti
