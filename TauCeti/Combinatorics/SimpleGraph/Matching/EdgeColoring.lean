/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.EdgeColoring

/-!
# Edge-colourings of simple graphs

This file identifies proper edge-colourings of a simple graph with proper edge-colourings of its
associated multigraph.  On the simple-graph side an edge-colouring is a vertex-colouring of the
line graph; this is the representation used by Mathlib's edge-colouring interface.  The
equivalence preserves every underlying unordered edge and every assigned colour.

As a consequence, Kőnig's edge-colouring theorem is stated directly through the simple graph's
line-graph colouring API: a finite simple bipartite graph is colourable with `k` edge colours
exactly when its maximum degree is at most `k`.

The interface follows the edge-colouring design of Mathlib PR #33313, without depending on that
unmerged proposal.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat.
  Természett. Ért. 34 (1916), 104--119.
-/

public section

universe u w

namespace SimpleGraph

variable {V : Type u} {C : Type w} {G : SimpleGraph V} {k : ℕ}

/-- Proper edge-colourings of a simple graph, represented as colourings of its line graph, are
equivalent to proper edge-colourings of the associated multigraph. -/
def edgeColoringEquivOfSimpleGraph (G : SimpleGraph V) (C : Type w) :
    (Graph.ofSimpleGraph G).EdgeColoring C ≃ G.lineGraph.Coloring C :=
  coloringCongr (Graph.lineGraphOfSimpleGraphIso G) (Equiv.refl C)

/-- Transporting a multigraph edge-colouring to the simple graph preserves the colour of the
corresponding edge. -/
@[simp]
theorem edgeColoringEquivOfSimpleGraph_apply
    (c : (Graph.ofSimpleGraph G).EdgeColoring C)
    (e : (Graph.ofSimpleGraph G).edgeSet) :
    edgeColoringEquivOfSimpleGraph G C c (Graph.lineGraphOfSimpleGraphIso G e) = c e := by
  simp [edgeColoringEquivOfSimpleGraph, coloringCongr, Iso.completeGraph]

/-- Transporting a simple-graph edge-colouring to the associated multigraph preserves the colour
of the corresponding edge. -/
@[simp]
theorem edgeColoringEquivOfSimpleGraph_symm_apply
    (c : G.lineGraph.Coloring C) (e : G.edgeSet) :
    (edgeColoringEquivOfSimpleGraph G C).symm c
      ((Graph.lineGraphOfSimpleGraphIso G).symm e) = c e := by
  simp [edgeColoringEquivOfSimpleGraph, coloringCongr, Iso.completeGraph]

/-- A simple graph has a proper edge-colouring by `C` exactly when its associated multigraph does.
The equivalence uses the same colours and keeps every underlying unordered edge. -/
theorem nonempty_lineGraph_coloring_iff_nonempty_edgeColoring_ofSimpleGraph :
    Nonempty (G.lineGraph.Coloring C) ↔
      Nonempty ((Graph.ofSimpleGraph G).EdgeColoring C) := by
  constructor
  · exact Nonempty.map (edgeColoringEquivOfSimpleGraph G C).symm
  · exact Nonempty.map (edgeColoringEquivOfSimpleGraph G C)

/-- **Kőnig's edge-colouring theorem for simple graphs.** A finite simple graph with a displayed
covering bipartition admits a proper edge-colouring by `k` colours exactly when its maximum degree
is at most `k`. -/
theorem lineGraph_colorable_iff_maxDegree_le [Fintype V] [DecidableRel G.Adj]
    {L R : Finset ↥(Graph.ofSimpleGraph G).vertexSet}
    (hLR : (Graph.ofSimpleGraph G).IsBipartition L R) :
    G.lineGraph.Colorable k ↔ G.maxDegree ≤ k := by
  rw [Colorable]
  exact nonempty_lineGraph_coloring_iff_nonempty_edgeColoring_ofSimpleGraph.trans
    (nonempty_edgeColoring_ofSimpleGraph_iff_maxDegree_le G hLR)

end SimpleGraph
