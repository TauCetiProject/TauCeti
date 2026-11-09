/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity

/-!
# Preservation of vertex and edge connectivity

This file records how vertex and edge connectivity of simple graphs behave under the elementary
operations used to build and dismantle connected graphs: deleting vertices, adjoining a vertex,
and adding edges. Deleting a set `s` of vertices is the subgraph `G.induce sᶜ` induced on the
remaining vertices, as in the definition of `SimpleGraph.IsVertexReachable`.

* Deleting a finite set of `m` vertices from an `(m + l)`-vertex-connected graph leaves an
  `l`-vertex-connected graph. Equivalently, deleting `m ≤ k` vertices from a `k`-vertex-connected
  graph leaves a `(k - m)`-vertex-connected graph.
* **Expansion lemma.** If deleting a vertex `x` leaves a `k`-vertex-connected graph and `x` has at
  least `k` neighbours, then the whole graph is `k`-vertex-connected. Adjoining a new vertex with
  at least `k` neighbours to a `k`-vertex-connected graph is the case where the graph with `x`
  deleted is the original one.
* Adding edges preserves `k`-vertex-connectivity (`SimpleGraph.IsVertexConnected.mono`) and
  `k`-edge-connectivity (`SimpleGraph.IsEdgeConnected.mono`).

None of these statements needs finiteness of the vertex type.

## Main results

* `SimpleGraph.IsVertexReachable.induce_compl`: two vertices outside a finite set `s` that are
  `(s.encard + l)`-vertex-reachable stay `l`-vertex-reachable after deleting `s`.
* `SimpleGraph.IsVertexConnected.induce_compl`: deleting a finite set `s` from an
  `(s.encard + l)`-vertex-connected graph leaves an `l`-vertex-connected graph.
* `SimpleGraph.IsVertexConnected.induce_compl_of_encard_le`: deleting a finite set `s` with
  `s.encard ≤ k` from a `k`-vertex-connected graph leaves a `(k - s.encard)`-vertex-connected
  graph.
* `SimpleGraph.isVertexConnected_of_induce_compl_singleton`: the expansion lemma.
* `SimpleGraph.IsEdgeConnected.mono`: edge connectivity is monotone in the graph.

## References

* D. B. West, *Introduction to Graph Theory*, 2nd ed., Prentice Hall, 2001, Section 4.2 (the
  expansion lemma).
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 1.4.
-/

public section

open Set.Notation

universe u

namespace SimpleGraph

variable {V : Type u} {G H : SimpleGraph V} {k l : ℕ∞} {s : Set V} {x : V}

/-! ### Deleting vertices -/

/-- Two vertices outside a finite vertex set `s` that are `(s.encard + l)`-vertex-reachable remain
`l`-vertex-reachable after deleting `s`. -/
theorem IsVertexReachable.induce_compl (hs : s.Finite) {u v : V} (hu : u ∉ s) (hv : v ∉ s)
    (h : G.IsVertexReachable (s.encard + l) u v) :
    (G.induce sᶜ).IsVertexReachable l ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [isVertexReachable_def] at h ⊢
  intro t ht htu htv
  -- Deleting `t` from `G.induce sᶜ` is deleting `s ∪ t` from `G`.
  have hst : (s ∪ Subtype.val '' t).encard < s.encard + l := by
    grw [Set.encard_union_le, Subtype.val_injective.encard_image]
    exact (ENat.add_lt_add_iff_left hs.encard_lt_top.ne).2 ht
  have hreach := h hst (by simp [hu, htu]) (by simp [hv, htv])
  let φ : G.induce (s ∪ Subtype.val '' t)ᶜ →g (G.induce sᶜ).induce tᶜ :=
    { toFun y := ⟨⟨y, by simpa using fun hy ↦ y.2 (.inl hy)⟩,
        by simpa using fun hy ↦ y.2 (.inr ⟨_, hy, rfl⟩)⟩
      map_rel' h := by simpa using h }
  exact hreach.map φ

/-- Deleting a finite set `s` of vertices from an `(s.encard + l)`-vertex-connected graph leaves
an `l`-vertex-connected graph. -/
theorem IsVertexConnected.induce_compl (hs : s.Finite)
    (h : G.IsVertexConnected (s.encard + l)) : (G.induce sᶜ).IsVertexConnected l := by
  refine isVertexConnected_def.2
    ⟨?_, fun u v ↦ (h.isVertexReachable u v).induce_compl hs u.2 v.2⟩
  have hcard := h.add_one_le_card
  rw [← Set.encard_add_encard_compl s, add_assoc] at hcard
  rw [ENat.card_coe_set_eq]
  exact (ENat.add_le_add_iff_left hs.encard_lt_top.ne).1 hcard

/-- Deleting a finite set `s` of at most `k` vertices from a `k`-vertex-connected graph leaves a
`(k - s.encard)`-vertex-connected graph. -/
theorem IsVertexConnected.induce_compl_of_encard_le (h : G.IsVertexConnected k) (hs : s.Finite)
    (hsk : s.encard ≤ k) : (G.induce sᶜ).IsVertexConnected (k - s.encard) :=
  IsVertexConnected.induce_compl hs <| by
    rwa [add_tsub_cancel_of_le hsk]

/-! ### Adjoining a vertex -/

/-- **Expansion lemma.** If deleting a vertex `x` leaves a `k`-vertex-connected graph and `x` has
at least `k` neighbours, then the graph is `k`-vertex-connected. This is the statement that
adjoining a new vertex `x` adjacent to at least `k` vertices of a `k`-vertex-connected graph gives
a `k`-vertex-connected graph, where the original graph is `G.induce {x}ᶜ`. -/
theorem isVertexConnected_of_induce_compl_singleton (h : (G.induce {x}ᶜ).IsVertexConnected k)
    (hx : k ≤ (G.neighborSet x).encard) : G.IsVertexConnected k := by
  refine isVertexConnected_iff.2 ⟨?_, fun s hs ↦ ?_⟩
  · grw [h.add_one_le_card, ENat.card_coe_set_eq]
    exact Set.encard_le_card
  -- After deleting `s`, any two remaining vertices other than `x` are reachable, through the
  -- graph with `x` deleted.
  have key (a b : ↥sᶜ) (ha : a.1 ≠ x) (hb : b.1 ≠ x) : (G.induce sᶜ).Reachable a b := by
    have hs' : ({x}ᶜ ↓∩ s).encard < k := (Set.encard_preimage_val_le_encard_right _ _).trans_lt hs
    have hreach := isVertexReachable_def.1 (h.isVertexReachable ⟨a, ha⟩ ⟨b, hb⟩) hs'
      (by exact a.2) (by exact b.2)
    let φ : (G.induce {x}ᶜ).induce ({x}ᶜ ↓∩ s)ᶜ →g G.induce sᶜ :=
      induceHom (Embedding.induce {x}ᶜ).toHom fun _ hy ↦ by simpa using hy
    exact hreach.map φ
  -- If `x` remains, it has a remaining neighbour, since fewer than `k` vertices were deleted.
  have hx' (a : ↥sᶜ) : ∃ c : ↥sᶜ, c.1 ≠ x ∧ (G.induce sᶜ).Reachable a c := by
    by_cases hax : a.1 = x
    · obtain ⟨w, hw, hws⟩ : ∃ w ∈ G.neighborSet x, w ∉ s := by
        by_contra! hN
        exact (hx.trans (Set.encard_le_encard hN)).not_gt hs
      refine ⟨⟨w, hws⟩, (G.ne_of_adj hw).symm, Adj.reachable ?_⟩
      simpa [hax] using hw
    · exact ⟨a, hax, .rfl⟩
  intro a b
  obtain ⟨c, hc, hac⟩ := hx' a
  obtain ⟨d, hd, hbd⟩ := hx' b
  exact hac.trans ((key c d hc hd).trans hbd.symm)

/-! ### Adding edges -/

/-- Edge connectivity is monotone in the graph: adding edges preserves `k`-edge-connectivity. -/
@[gcongr]
theorem IsEdgeConnected.mono (hGH : G ≤ H) (h : G.IsEdgeConnected k) :
    H.IsEdgeConnected k :=
  fun u v ↦ (h u v).mono hGH

end SimpleGraph
