/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

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
* `SimpleGraph.Walk.exists_weight_eq_minEdgeWeight`: some traversed edge attains the minimum.
* `SimpleGraph.Walk.le_minEdgeWeight_iff`: the universal property of the minimum.
* `SimpleGraph.Adj.minEdgeWeight_toWalk`: the minimum on a one-edge walk.
* `SimpleGraph.Walk.minEdgeWeight_reverse`: reversal does not change the minimum.
* `SimpleGraph.Walk.minEdgeWeight_map`: mapping a walk pulls the edge weights back.
* `SimpleGraph.Walk.minEdgeWeight_cons`: the minimum after prepending an edge.
* `SimpleGraph.Walk.minEdgeWeight_append`: the minimum after appending two nonempty walks.
-/

public section

namespace SimpleGraph.Walk

universe u v u'

variable {V : Type u} {V' : Type u'} {K : Type v} {G H : SimpleGraph V}
  {G' : SimpleGraph V'} {u v w : V}

/-- Mapping a weight function over the edges of a nonempty walk gives a nonempty list. -/
theorem map_edges_ne_nil (p : G.Walk u v) (wt : Sym2 V → K) (hp : ¬p.Nil) :
    p.edges.map wt ≠ [] := by
  simpa using (p.edges_eq_nil.not.mpr hp)

/-- The minimum weight of an edge traversed by a nonempty walk.

Repeated edge identities and distinct edges of equal weight are harmless: the definition takes the
minimum of the list of edge weights. -/
def minEdgeWeight [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) : K :=
  (p.edges.map wt).min (p.map_edges_ne_nil wt hp)

/-- The minimum edge weight is the minimum of the list of weights of the traversed edges. -/
theorem minEdgeWeight_def [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) :
    p.minEdgeWeight wt hp =
      (p.edges.map wt).min (p.map_edges_ne_nil wt hp) :=
  (rfl)

/-- Some edge of a nonempty walk attains its minimum edge weight. -/
theorem exists_weight_eq_minEdgeWeight [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) : ∃ e ∈ p.edges, wt e = p.minEdgeWeight wt hp := by
  unfold minEdgeWeight
  obtain ⟨e, he, hwt⟩ := List.mem_map.mp (List.min_mem (p.map_edges_ne_nil wt hp))
  exact ⟨e, he, hwt⟩

/-- The minimum edge weight of a walk is at most the weight of every traversed edge. -/
theorem minEdgeWeight_le [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) {e : Sym2 V} (he : e ∈ p.edges) : p.minEdgeWeight wt hp ≤ wt e := by
  unfold minEdgeWeight
  exact List.min_le_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)

grind_pattern minEdgeWeight_le => p.minEdgeWeight wt hp, e ∈ p.edges

/-- A value is at most the minimum edge weight exactly when it is at most the weight of every edge
of the walk. -/
theorem le_minEdgeWeight_iff [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) (k : K) :
    k ≤ p.minEdgeWeight wt hp ↔ ∀ e ∈ p.edges, k ≤ wt e := by
  simp only [minEdgeWeight, List.le_min_iff, List.forall_mem_map]

/-- Two nonempty walks have the same minimum edge weight when they traverse the same edges. -/
theorem minEdgeWeight_congr [LinearOrder K] {x y : V}
    {p : G.Walk u v} {q : H.Walk x y} (wt : Sym2 V → K) (hp : ¬p.Nil) (hq : ¬q.Nil)
    (h : ∀ e, e ∈ p.edges ↔ e ∈ q.edges) :
    p.minEdgeWeight wt hp = q.minEdgeWeight wt hq := by
  apply eq_of_forall_le_iff
  intro k
  rw [p.le_minEdgeWeight_iff wt hp, q.le_minEdgeWeight_iff wt hq]
  constructor
  · exact fun hk e he ↦ hk e ((h e).2 he)
  · exact fun hk e he ↦ hk e ((h e).1 he)

/-- The minimum edge weight of the one-edge walk associated to an adjacency is that edge's
weight. -/
@[simp]
theorem _root_.SimpleGraph.Adj.minEdgeWeight_toWalk [LinearOrder K] (h : G.Adj u v)
    (wt : Sym2 V → K) :
    h.toWalk.minEdgeWeight wt (h.toWalk.not_nil_of_ne h.ne) = wt s(u, v) := by
  unfold Walk.minEdgeWeight
  simp

/-- Reversing a nonempty walk does not change its minimum edge weight. -/
@[simp]
theorem minEdgeWeight_reverse [LinearOrder K] (p : G.Walk u v) (wt : Sym2 V → K)
    (hp : ¬p.Nil) :
    p.reverse.minEdgeWeight wt (by simpa using hp) = p.minEdgeWeight wt hp := by
  apply minEdgeWeight_congr wt
  intro e
  simp

/-- Mapping a nonempty walk pulls its edge weights back along the vertex map. -/
@[simp]
theorem minEdgeWeight_map [LinearOrder K] (p : G.Walk u v) (f : G →g G')
    (wt : Sym2 V' → K) (hp : ¬p.Nil) :
    (p.map f).minEdgeWeight wt (by simpa using hp) =
      p.minEdgeWeight (wt ∘ Sym2.map f) hp := by
  unfold minEdgeWeight
  simp only [edges_map, List.map_map]

/-- Prepending an edge to a nonempty walk takes the minimum of its weight and the old minimum
edge weight. -/
@[simp]
theorem minEdgeWeight_cons [LinearOrder K] (h : G.Adj u v) (p : G.Walk v w)
    (wt : Sym2 V → K) (hp : ¬p.Nil) :
    (p.cons h).minEdgeWeight wt (by simp) = min (wt s(u, v)) (p.minEdgeWeight wt hp) := by
  apply eq_of_forall_le_iff
  intro k
  rw [(p.cons h).le_minEdgeWeight_iff, le_min_iff, p.le_minEdgeWeight_iff]
  simp

/-- Appending two nonempty walks takes the minimum of their minimum edge weights. -/
@[simp]
theorem minEdgeWeight_append [LinearOrder K] (p : G.Walk u v) (q : G.Walk v w)
    (wt : Sym2 V → K) (hp : ¬p.Nil) (hq : ¬q.Nil) :
    (p.append q).minEdgeWeight wt (by simp [hp]) =
      min (p.minEdgeWeight wt hp) (q.minEdgeWeight wt hq) := by
  apply eq_of_forall_le_iff
  intro k
  rw [(p.append q).le_minEdgeWeight_iff, le_min_iff, p.le_minEdgeWeight_iff,
    q.le_minEdgeWeight_iff]
  constructor
  · exact fun h ↦ ⟨fun e he ↦ h e (by simp [he]), fun e he ↦ h e (by simp [he])⟩
  · rintro ⟨hp', hq'⟩ e he
    rw [edges_append, List.mem_append] at he
    exact he.elim (hp' e) (hq' e)

end SimpleGraph.Walk
