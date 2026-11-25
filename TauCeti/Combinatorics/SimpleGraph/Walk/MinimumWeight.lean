/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Data.Finset.Max

/-!
# Minimum edge weight of a walk

This file defines the minimum weight of an edge traversed by a nonempty walk in a simple graph.
The operation depends only on the set of traversed edges, so repeated traversals do not affect it.
Its characteristic API gives an edge attaining the minimum and identifies the minimum as the
greatest lower bound of all edge weights along the walk.

Minimum edge weight is unchanged by reversing a walk or regarding it as a walk in a larger graph.
For a walk obtained by prepending an edge to a nonempty walk, it is the minimum of the new edge
weight and the old minimum. These facts let weighted-tree arguments use a named path quantity
instead of carrying a minimizing edge and a lower-bound property separately.

## Main definitions and results

* `SimpleGraph.Walk.minEdgeWeight`: the minimum edge weight along a nonempty walk.
* `SimpleGraph.Walk.minEdgeWeight_mem`: some traversed edge attains the minimum.
* `SimpleGraph.Walk.le_minEdgeWeight_iff`: the universal property of the minimum.
* `SimpleGraph.Adj.minEdgeWeight_toWalk`: the minimum on a one-edge walk.
* `SimpleGraph.Walk.minEdgeWeight_reverse`: reversal does not change the minimum.
* `SimpleGraph.Walk.minEdgeWeight_mapLe`: inclusion into a larger graph does not change it.
* `SimpleGraph.Walk.minEdgeWeight_cons`: the minimum after prepending an edge.
-/

public section

open Finset

namespace SimpleGraph.Walk

universe u v

variable {V : Type u} {K : Type v} {G H : SimpleGraph V} {u v w : V}

/-- The minimum weight of an edge traversed by a nonempty walk.

Repeated edge identities and distinct edges of equal weight are harmless: the definition takes the
minimum of the image of the walk's edge finset. -/
noncomputable def minEdgeWeight [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) : K := by
  classical
  exact (p.edges.toFinset.image wt).min' (by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges (p.edges_eq_nil.not.mpr hp)
    exact ⟨wt e, mem_image.2 ⟨e, List.mem_toFinset.2 he, rfl⟩⟩)

/-- Some edge of a nonempty walk attains its minimum edge weight. -/
theorem minEdgeWeight_mem [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) : ∃ e ∈ p.edges, wt e = p.minEdgeWeight wt hp := by
  classical
  unfold minEdgeWeight
  obtain ⟨e, he, hwt⟩ := mem_image.mp
    (Finset.min'_mem (p.edges.toFinset.image wt) _)
  exact ⟨e, List.mem_toFinset.1 he, hwt⟩

/-- The minimum edge weight of a walk is at most the weight of every traversed edge. -/
theorem minEdgeWeight_le [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) {e : Sym2 V} (he : e ∈ p.edges) : p.minEdgeWeight wt hp ≤ wt e := by
  classical
  unfold minEdgeWeight
  exact Finset.min'_le (p.edges.toFinset.image wt) (wt e)
    (mem_image.2 ⟨e, List.mem_toFinset.2 he, rfl⟩)

/-- A value is at most the minimum edge weight exactly when it is at most the weight of every edge
of the walk. -/
theorem le_minEdgeWeight_iff [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) (k : K) :
    k ≤ p.minEdgeWeight wt hp ↔ ∀ e ∈ p.edges, k ≤ wt e := by
  classical
  constructor
  · exact fun hk e he ↦ hk.trans (p.minEdgeWeight_le wt hp he)
  · intro hk
    unfold minEdgeWeight
    apply Finset.le_min' (p.edges.toFinset.image wt) _ k
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_image.mp hy
    exact hk e (List.mem_toFinset.1 he)

/-- Two nonempty walks have the same minimum edge weight when they traverse the same edges. -/
theorem minEdgeWeight_congr [LinearOrder K] {x y : V}
    {p : G.Walk u v} {q : H.Walk x y} (wt : Sym2 V → K) (hp : ¬p.Nil) (hq : ¬q.Nil)
    (h : ∀ e, e ∈ p.edges ↔ e ∈ q.edges) :
    p.minEdgeWeight wt hp = q.minEdgeWeight wt hq := by
  apply le_antisymm
  · obtain ⟨e, he, hwt⟩ := q.minEdgeWeight_mem wt hq
    exact (p.minEdgeWeight_le wt hp ((h e).2 he)).trans_eq hwt
  · obtain ⟨e, he, hwt⟩ := p.minEdgeWeight_mem wt hp
    exact (q.minEdgeWeight_le wt hq ((h e).1 he)).trans_eq hwt

/-- The minimum edge weight of the one-edge walk associated to an adjacency is that edge's
weight. -/
@[simp]
theorem _root_.SimpleGraph.Adj.minEdgeWeight_toWalk [LinearOrder K] (h : G.Adj u v)
    (wt : Sym2 V → K) :
    h.toWalk.minEdgeWeight wt (h.toWalk.not_nil_of_ne h.ne) = wt s(u, v) := by
  apply le_antisymm
  · exact minEdgeWeight_le _ _ _ (by simp)
  · rw [le_minEdgeWeight_iff]
    simp

/-- Reversing a nonempty walk does not change its minimum edge weight. -/
@[simp]
theorem minEdgeWeight_reverse [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) :
    p.reverse.minEdgeWeight wt (by simpa using hp) = p.minEdgeWeight wt hp := by
  apply minEdgeWeight_congr wt
  intro e
  simp

/-- Regarding a nonempty walk as a walk in a larger graph does not change its minimum edge
weight. -/
@[simp]
theorem minEdgeWeight_mapLe [LinearOrder K] (p : G.Walk u v) (hGH : G ≤ H)
    (wt : Sym2 V → K) (hp : ¬p.Nil) :
    (p.mapLe hGH).minEdgeWeight wt (by simpa using hp) = p.minEdgeWeight wt hp := by
  apply minEdgeWeight_congr wt
  intro e
  rw [edges_mapLe_eq_edges]

/-- Prepending an edge to a nonempty walk takes the minimum of its weight and the old minimum
edge weight. -/
theorem minEdgeWeight_cons [LinearOrder K] (h : G.Adj u v) (p : G.Walk v w)
    (wt : Sym2 V → K) (hp : ¬p.Nil) :
    (p.cons h).minEdgeWeight wt (by simp) = min (wt s(u, v)) (p.minEdgeWeight wt hp) := by
  apply le_antisymm
  · refine le_min (minEdgeWeight_le _ _ _ (by simp)) ?_
    obtain ⟨e, he, hwt⟩ := p.minEdgeWeight_mem wt hp
    exact (minEdgeWeight_le _ _ _ (by simp [he])).trans_eq hwt
  · rw [le_minEdgeWeight_iff]
    intro e he
    simp only [edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (p.minEdgeWeight_le wt hp he)

end SimpleGraph.Walk
