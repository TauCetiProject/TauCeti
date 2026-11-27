/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Colour graphs of edge labellings

For an edge labelling `C` of a graph and a label `k`, Mathlib's `C.labelGraph k` is the graph of
the edges labelled `k`. The degrees of these graphs at a vertex sum to its degree in the original
graph (`SimpleGraph.EdgeLabeling.sum_degree_labelGraph`); for a labelling of a complete graph this
gives `Fintype.card V - 1` (`SimpleGraph.TopEdgeLabeling.sum_degree_labelGraph`).

This file also computes colour graphs for two operations on labellings: pulling a labelling back
along a graph homomorphism (`SimpleGraph.EdgeLabeling.pullback`), which gives the pulled-back graph
intersected with the source graph, with the special cases of a graph embedding and of restricting
a labelling of the complete graph along an injection of vertices
(`SimpleGraph.TopEdgeLabeling.pullback`); and composing with an injective map of labels
(`SimpleGraph.EdgeLabeling.compRight`), which keeps the graph of each label. These are the facts
needed to move monochromatic cliques between colourings, as in Ramsey theory.
-/

public section

open Finset

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

/-- The degrees at a vertex of all colour graphs of an edge labelling sum to its degree in the
original graph. -/
theorem EdgeLabeling.sum_degree_labelGraph [Fintype V] [Fintype K] [DecidableRel G.Adj]
    [DecidableEq K] (C : EdgeLabeling G K) (v : V) :
    ∑ k, (C.labelGraph k).degree v = G.degree v := by
  classical
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  rw [← card_biUnion (t := fun k ↦ {w | (C.labelGraph k).Adj v w})
    fun k _ l _ hkl ↦ disjoint_filter.2 fun w _ hk hl ↦
      SimpleGraph.disjoint_left.1 (EdgeLabeling.pairwise_disjoint_labelGraph hkl) _ _ hk hl]
  congr 1
  ext w
  simp [EdgeLabeling.labelGraph_adj]

/-- The degrees at a vertex of all colour graphs of a complete-graph edge labelling sum to one less
than the number of vertices. -/
theorem TopEdgeLabeling.sum_degree_labelGraph [Fintype V] [DecidableEq V] [Fintype K]
    [DecidableEq K]
    (C : TopEdgeLabeling V K) (v : V) :
    ∑ k, (C.labelGraph k).degree v = Fintype.card V - 1 := by
  rw [EdgeLabeling.sum_degree_labelGraph, complete_graph_degree]

/-- Relabelling the edges along an injective map of labels does not change the graph of the edges
of a given label. -/
theorem EdgeLabeling.labelGraph_compRight_of_injective (C : EdgeLabeling G K) {g : K → K'}
    (hg : Function.Injective g) (k : K) : (C.compRight g).labelGraph (g k) = C.labelGraph k := by
  ext x y
  simp [EdgeLabeling.labelGraph_adj, hg.eq_iff]

/-- The graph of the edges of label `k` of a labelling pulled back along a graph homomorphism
`f : G' →g G` consists of the edges of `G'` whose image under `f` has label `k`. -/
theorem EdgeLabeling.labelGraph_pullback (C : EdgeLabeling G K) (f : G' →g G) (k : K) :
    (C.pullback f).labelGraph k = G' ⊓ (C.labelGraph k).comap f := by
  ext x y
  have hf (h : G'.Adj x y) : f.mapEdgeSet ⟨s(x, y), h⟩ = ⟨s(f x, f y), f.map_adj h⟩ :=
    Subtype.ext (Hom.mapEdgeSet_coe ..)
  simp only [EdgeLabeling.labelGraph_adj, EdgeLabeling.pullback_apply, inf_adj, comap_adj]
  exact ⟨fun ⟨h, hk⟩ ↦ ⟨h, f.map_adj h, hf h ▸ hk⟩, fun ⟨h, _, hk⟩ ↦ ⟨h, hf h ▸ hk⟩⟩

/-- The graph of the edges of label `k` of a labelling pulled back along a graph embedding is the
pullback of the graph of the edges of label `k`. -/
theorem EdgeLabeling.labelGraph_pullback_toRelHom (C : EdgeLabeling G K) (f : G' ↪g G) (k : K) :
    (C.pullback f.toRelHom).labelGraph k = (C.labelGraph k).comap f := by
  rw [labelGraph_pullback, RelEmbedding.coe_toRelHom, inf_eq_right]
  exact fun x y h ↦ f.map_adj_iff.1 (C.labelGraph_le h)

/-- The graph of the edges of label `k` of a labelling restricted along an injection of vertices is
the pullback of the graph of the edges of label `k`. -/
@[simp]
theorem TopEdgeLabeling.labelGraph_pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) (k : K) :
    (C.pullback f).labelGraph k = (C.labelGraph k).comap f := by
  simp [EdgeLabeling.labelGraph_pullback]

end SimpleGraph
