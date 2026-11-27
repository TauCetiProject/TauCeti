/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Colour graphs of edge labellings under pullback and relabelling

For an edge labelling `C` of a graph and a label `k`, Mathlib's `C.labelGraph k` is the graph of
the edges labelled `k`. This file computes that graph for two operations on labellings:
pulling a labelling back along a graph homomorphism (`SimpleGraph.EdgeLabeling.pullback`), which
gives the pulled-back graph intersected with the source graph, with the special cases of a graph
embedding and of restricting a labelling of the complete graph along an injection of vertices
(`SimpleGraph.TopEdgeLabeling.pullback`); and composing with an injective map of labels
(`SimpleGraph.EdgeLabeling.compRight`), which keeps the graph of each label. These are the facts
needed to move monochromatic cliques between colourings, as in Ramsey theory.
-/

public section

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

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
