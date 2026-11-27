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
the edges labelled `k`. This file computes that graph for the two operations Mathlib provides on
labellings: restricting a labelling of the complete graph along an injection of vertices
(`SimpleGraph.TopEdgeLabeling.pullback`), which gives the pulled-back graph, and composing with an
injective map of labels (`SimpleGraph.EdgeLabeling.compRight`), which keeps the graph of each
label. These are the facts needed to move monochromatic cliques between colourings, as in Ramsey
theory.
-/

public section

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {K K' : Type*}

/-- Relabelling the edges along an injective map of labels does not change the graph of the edges
of a given label. -/
theorem EdgeLabeling.labelGraph_compRight_of_injective (C : EdgeLabeling G K) {g : K → K'}
    (hg : Function.Injective g) (k : K) : (C.compRight g).labelGraph (g k) = C.labelGraph k := by
  ext x y
  simp [EdgeLabeling.labelGraph_adj, hg.eq_iff]

/-- The graph of the edges of label `k` of a labelling restricted along an injection of vertices is
the pullback of the graph of the edges of label `k`. -/
@[simp]
theorem TopEdgeLabeling.labelGraph_pullback (C : TopEdgeLabeling V K) (f : V' ↪ V) (k : K) :
    (C.pullback f).labelGraph k = (C.labelGraph k).comap f := by
  ext x y
  simp [EdgeLabeling.get_eq, Hom.mapEdgeSet]

end SimpleGraph
