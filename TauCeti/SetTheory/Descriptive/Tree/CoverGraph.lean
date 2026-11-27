/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.SetTheory.Descriptive.Tree.Order

/-!
# The cover graph of a tree order

For a tree order `r` (`TauCeti.IsTreeOrder`: a partial order with a least element whose principal
down-sets are finite chains), the *cover graph* joins `u` and `v` when one covers the other; it
is the simple graph `SimpleGraph.fromRel (RelCovBy r)`. This file shows that the cover graph is a
tree, and that the order is recovered from the graph and its least element: `x ≤ y` exactly when
`x` lies on the path from the least element to `y`. So a graph isomorphism between the cover
graphs of two tree orders that maps least element to least element is an isomorphism of the
orders.

Every element `y` other than the least element covers exactly one element, its *parent*: the
largest element of the finite chain of strict predecessors of `y`. Following parents down from
`y` gives a path from the least element to `y` whose vertices are the predecessors of `y`. The
graph is acyclic because each vertex has at most one neighbour with at most as many predecessors
as itself: its parent.

## Main results

* `TauCeti.IsTreeOrder.exists_isPath_support`: the path of parents from the least element to `y`
  passes exactly through the predecessors of `y`.
* `TauCeti.IsTreeOrder.isTree_fromRel_relCovBy`: the cover graph of a tree order is a tree.
* `TauCeti.IsTreeOrder.mem_support_iff_rel`: on every path from the least element to `y`, the
  vertices are exactly the predecessors of `y`.
* `TauCeti.IsTreeOrder.rel_iff_of_iso`: an isomorphism of cover graphs of tree orders mapping
  least element to least element is an isomorphism of the orders.
-/

public section

open SimpleGraph

namespace TauCeti

variable {V W : Type*}

namespace IsTreeOrder

variable {r : V → V → Prop} (h : IsTreeOrder r)
include h

/-- **The path of parents.** In the cover graph of a tree order with least element `a`, there is
a path from `a` to `y` whose vertices are exactly the predecessors of `y`. -/
theorem exists_isPath_support {a : V} (ha : ∀ x, r a x) (y : V) :
    ∃ p : (SimpleGraph.fromRel (RelCovBy r)).Walk a y, p.IsPath ∧
      ∀ x, x ∈ p.support ↔ r x y := by
  have := h.isPartialOrder
  induction y using h.wellFounded.induction with
  | _ y ih =>
  by_cases hya : y = a
  · subst hya
    exact ⟨.nil, .nil, fun x => by
      simpa using ⟨fun hx => hx ▸ refl_of r x, fun hx => antisymm_of r hx (ha x)⟩⟩
  obtain ⟨q, hq⟩ := h.exists_relCovBy (ha y) (Ne.symm hya)
  obtain ⟨p, hp, hsupp⟩ := ih q ⟨hq.rel, hq.not_rel⟩
  have hadj : (SimpleGraph.fromRel (RelCovBy r)).Adj q y :=
    (SimpleGraph.fromRel_adj _ _ _).2 ⟨hq.ne, .inl hq⟩
  refine ⟨p.concat hadj, hp.concat (fun hy => hq.not_rel ((hsupp y).1 hy)) hadj, fun x => ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton, hsupp]
  refine ⟨fun hx => hx.elim (fun hxq => trans_of r hxq hq.rel) fun hxy => hxy ▸ refl_of r y,
    fun hxy => ?_⟩
  by_cases hx : x = y
  · exact .inr hx
  · exact .inl (h.rel_of_relCovBy hq hxy hx)

/-- The cover graph of a tree order is connected. -/
theorem connected_fromRel_relCovBy : (SimpleGraph.fromRel (RelCovBy r)).Connected := by
  obtain ⟨a, ha⟩ := h.exists_forall
  have hreach (y : V) : (SimpleGraph.fromRel (RelCovBy r)).Reachable a y :=
    let ⟨p, _⟩ := h.exists_isPath_support ha y
    ⟨p⟩
  exact (connected_iff_exists_forall_reachable _).2 ⟨a, hreach⟩

/-- The cover graph of a tree order is acyclic. -/
theorem isAcyclic_fromRel_relCovBy : (SimpleGraph.fromRel (RelCovBy r)).IsAcyclic := by
  have := h.isPartialOrder
  have hcov {v u : V} (hvu : (SimpleGraph.fromRel (RelCovBy r)).Adj v u)
      (hle : {w | r w u}.ncard ≤ {w | r w v}.ncard) : RelCovBy r u v :=
    ((SimpleGraph.fromRel_adj _ _ _).1 hvu).2.resolve_left fun hvu' =>
      (h.ncard_lt_ncard_of_rel_of_not_rel hvu'.rel hvu'.not_rel).not_ge hle
  exact isAcyclic_of_forall_adj_le_eq (fun v => {w | r w v}.ncard)
    fun _ _ _ hu hw hu' hw' => h.eq_of_relCovBy (hcov hu hu') (hcov hw hw')

/-- **The cover graph of a tree order is a tree.** -/
theorem isTree_fromRel_relCovBy : (SimpleGraph.fromRel (RelCovBy r)).IsTree :=
  ⟨h.connected_fromRel_relCovBy, h.isAcyclic_fromRel_relCovBy⟩

/-- **The order of a tree order is read off its cover graph.** On every path from the least
element `a` to `y` in the cover graph, the vertices are exactly the predecessors of `y`. -/
theorem mem_support_iff_rel {a y : V} (ha : ∀ x, r a x)
    (p : (SimpleGraph.fromRel (RelCovBy r)).Walk a y) (hp : p.IsPath) (x : V) :
    x ∈ p.support ↔ r x y := by
  obtain ⟨q, hq, hsupp⟩ := h.exists_isPath_support ha y
  have : (⟨p, hp⟩ : (SimpleGraph.fromRel (RelCovBy r)).Path a y) = ⟨q, hq⟩ :=
    (h.isAcyclic_fromRel_relCovBy.subsingleton_path a y).elim _ _
  rw [show p = q from congrArg Subtype.val this, hsupp]

omit h in
/-- **Cover graphs determine tree orders.** A graph isomorphism between the cover graphs of tree
orders `r` and `s` mapping a least element of `r` to a least element of `s` is an isomorphism of
the orders. -/
theorem rel_iff_of_iso {s : W → W → Prop} (hr : IsTreeOrder r) (hs : IsTreeOrder s)
    (σ : SimpleGraph.fromRel (RelCovBy r) ≃g SimpleGraph.fromRel (RelCovBy s)) {a : V}
    (ha : ∀ x, r a x) (hσa : ∀ x, s (σ a) x) (x y : V) : s (σ x) (σ y) ↔ r x y := by
  obtain ⟨p, hp, hsupp⟩ := hr.exists_isPath_support ha y
  have hpm : (p.map σ.toHom).IsPath := hp.map σ.injective
  have key := hs.mem_support_iff_rel hσa (p.map σ.toHom) hpm (σ x)
  rw [Walk.support_map, List.mem_map] at key
  refine key.symm.trans ((hsupp x).symm.trans ?_).symm
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨z, hz, hzx⟩ => σ.injective hzx ▸ hz⟩

end IsTreeOrder

end TauCeti
