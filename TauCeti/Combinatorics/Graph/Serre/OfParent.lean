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
its parent `p v`. A reduced path in this graph first climbs along the parent map and then
descends, without passing twice through the same edge at its top. Hence the graph is a forest as
soon as no vertex is a proper iterated parent of itself, and it is a tree when moreover any two
vertices have a common iterated parent. Rooted trees, and the trees attached by Serre to an
increasing union of subgroups, are of this form.

A group acting on `V` and commuting with the parent map acts on the graph by automorphisms that
preserve the orientation of every edge towards the parent.

## Main declarations

* `TauCeti.SerreGraph.ofParent`: the Serre graph of a parent map.
* `TauCeti.SerreGraph.exists_iterate_eq_of_isReduced`: the shape of reduced paths.
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
`(v, false)` from `p v` to `v`. -/
@[expose] def ofParent : SerreGraph.{u, u} where
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

/-- The parent map, as a map on the vertices of its graph. -/
private def parent (v : (ofParent p).V) : (ofParent p).V := p v

/-- The shape of a reduced path, together with the constraints on the darts that can extend it:
the path climbs `k` steps and then descends `l` steps, after a descent it cannot climb again,
and a descent from the top of a climb does not return along the last dart. -/
private def IsClimbDescent {a b : (ofParent p).V} (q : (ofParent p).Path a b) (k l : ℕ) : Prop :=
  k + l = q.length ∧ (parent p)^[k] a = (parent p)^[l] b ∧
    (0 < k → 0 < l → (parent p)^[k - 1] a ≠ (parent p)^[l - 1] b) ∧
    ∀ {c : (ofParent p).V} (e : Quiver.Hom b c), Path.IsReduced (ofParent p) (q.cons e) →
      if e.1.2 then l = 0 else l = 0 → 0 < k → (parent p)^[k - 1] a ≠ c

variable {p} in
/-- Extending a reduced path by a descending dart lengthens its descent. -/
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
  · -- A dart climbing from `c` would reverse the last dart.
    obtain ⟨⟨x, d⟩, hs, ht⟩ := e
    cases d
    · simp
    · obtain rfl : x = c := hs
      exact absurd rfl ((Path.isReduced_cons_cons _ _ _ _).mp he).2

variable {p} in
/-- A reduced path can only be extended by a climbing dart if it has not descended yet, and
then its climb is lengthened. -/
private theorem IsClimbDescent.cons_true {a b : (ofParent p).V} {q : (ofParent p).Path a b}
    {k l : ℕ} (h : IsClimbDescent p q k l)
    (hq : Path.IsReduced (ofParent p)
      (q.cons (⟨(b, true), rfl, rfl⟩ : Quiver.Hom b (parent p b)))) :
    IsClimbDescent p (q.cons (⟨(b, true), rfl, rfl⟩ : Quiver.Hom b (parent p b))) (k + 1) 0 := by
  obtain ⟨hkl, heq, -, hext⟩ := h
  obtain rfl : l = 0 := hext _ hq
  refine ⟨by rw [Quiver.Path.length_cons]; omega,
    by rw [Function.iterate_succ_apply', heq]; rfl, by simp, fun e he => ?_⟩
  -- A dart descending from the parent of `b` does not return to `b`.
  obtain ⟨⟨x, d⟩, hs, ht⟩ := e
  cases d
  · have hx : (x, false) ≠ (b, false) := ((Path.isReduced_cons_cons _ _ _ _).mp he).2
    obtain rfl : x = _ := ht
    intro _ _ h
    exact hx (by rw [← h, Nat.add_sub_cancel, heq]; rfl)
  · rfl

/-- Every reduced path climbs and then descends. -/
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

/-- A reduced path of the graph of a parent map climbs `k` steps and then descends `l` steps,
and the last vertex of the climb below the top differs from the first vertex of the descent. -/
theorem exists_iterate_eq_of_isReduced {a b : V} (q : (ofParent p).Path a b)
    (hq : Path.IsReduced (ofParent p) q) :
    ∃ k l, k + l = q.length ∧ p^[k] a = p^[l] b ∧
      (0 < k → 0 < l → p^[k - 1] a ≠ p^[l - 1] b) := by
  obtain ⟨k, l, hkl, heq, hne, -⟩ := exists_isClimbDescent p q hq
  exact ⟨k, l, hkl, heq, hne⟩

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
theorem ofParent_preconnected_iff :
    (ofParent p).Preconnected ↔ ∀ a b : V, ∃ m n, p^[m] a = p^[n] b := by
  rw [preconnected_iff]
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · obtain ⟨q⟩ := h a b
    obtain ⟨k, l, -, heq, -⟩ :=
      exists_iterate_eq_of_isReduced p _ (Path.isReduced_reduce (ofParent p) q)
    exact ⟨k, l, heq⟩
  · obtain ⟨m, n, hmn⟩ := h a b
    obtain ⟨q⟩ := ofParent_nonempty_path_iterate p a m
    obtain ⟨r⟩ := ofParent_nonempty_path_iterate p b n
    rw [hmn] at q
    exact ⟨q.comp r.reverse⟩

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

/-- The action on the graph of a parent map has no inversions: it preserves the orientation of
each edge towards the parent. -/
theorem ofParentAction_equivE_ne_rev (h : ∀ (g : G) (v : V), p (g • v) = g • p v) (g : G)
    (e : V × Bool) : (ofParentAction p h g).equivE e ≠ (ofParent p).rev e := by
  rw [ofParentAction_equivE]
  exact fun h' => Bool.not_ne_self e.2 (congrArg Prod.snd h').symm

end SerreGraph
end TauCeti
