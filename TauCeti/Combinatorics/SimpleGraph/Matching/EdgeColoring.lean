/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.EdgeColoring

/-!
# Edge-colouring bipartite simple graphs

An edge-colouring of a simple graph is a vertex colouring of its line graph. This module gives
that construction its standard names and transports Kőnig's edge-colouring theorem from the
edge-labelled multigraph `Graph.ofSimpleGraph G` back to `G`.

For a finite bipartite simple graph, edge-colourability by `k` colours is equivalent to every
vertex having degree at most `k`, and the chromatic index is the maximum degree. The results use
`SimpleGraph.IsBipartite`, so isolated vertices need not be assigned to displayed bipartition
classes in advance.

The core `EdgeColoring`, `EdgeColorableWith`, `EdgeColorable`, and `chromaticIndex` interface is
adapted from [Mathlib pull request #33313](https://github.com/leanprover-community/mathlib4/pull/33313)
by Snir Broshi. It is included here while that proposal remains unmerged.

## Main results

* `SimpleGraph.edgeColoringEquivOfSimpleGraph`: proper edge-colourings agree with those of the
  associated edge-labelled multigraph.
* `SimpleGraph.IsBipartite.exists_isBipartition_ofSimpleGraph`: a finite bipartite simple graph
  supplies the displayed bipartition required by the multigraph API.
* `SimpleGraph.IsBipartite.edgeColorable_iff_maxDegree_le`: Kőnig's edge-colouring theorem.
* `SimpleGraph.IsBipartite.chromaticIndex_eq_maxDegree`: the chromatic index of a finite bipartite
  simple graph is its maximum degree.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat.
  Természett. Ért. 34 (1916), 104--119.
-/

public section

open scoped Graph

universe u w

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {C : Type w} {k : ℕ}

/-- A proper edge-colouring of a simple graph is a colouring of its line graph. -/
abbrev EdgeColoring (G : SimpleGraph V) (C : Type w) : Type (max u w) :=
  G.lineGraph.Coloring C

/-- A simple graph is edge-colourable with `C` when it has a proper edge-colouring by `C`. -/
abbrev EdgeColorableWith (G : SimpleGraph V) (C : Type w) : Prop :=
  Nonempty (G.EdgeColoring C)

/-- A simple graph is edge-colourable by at most `k` colours when it has a proper edge-colouring
by `Fin k`. -/
abbrev EdgeColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.EdgeColorableWith (Fin k)

/-- The chromatic index of a simple graph is the chromatic number of its line graph. -/
noncomputable abbrev chromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

/-- Proper edge-colourings of a simple graph are equivalent to proper edge-colourings of its
associated edge-labelled multigraph. -/
def edgeColoringEquivOfSimpleGraph (G : SimpleGraph V) (C : Type w) :
    (Graph.ofSimpleGraph G).EdgeColoring C ≃ G.EdgeColoring C where
  toFun c := c.comp (Graph.lineGraphOfSimpleGraphIso G).symm.toHom
  invFun c := c.comp (Graph.lineGraphOfSimpleGraphIso G).toHom
  left_inv c := RelHom.ext (congrArg c <|
    RelIso.symm_apply_apply (Graph.lineGraphOfSimpleGraphIso G) ·)
  right_inv c := RelHom.ext (congrArg c <|
    RelIso.apply_symm_apply (Graph.lineGraphOfSimpleGraphIso G) ·)

/-- Transporting a multigraph edge-colouring to the simple graph evaluates it on the
corresponding actual edge. -/
@[simp]
theorem edgeColoringEquivOfSimpleGraph_apply
    (c : (Graph.ofSimpleGraph G).EdgeColoring C) (e : G.edgeSet) :
    edgeColoringEquivOfSimpleGraph G C c e =
      c ((Graph.lineGraphOfSimpleGraphIso G).symm e) :=
  (rfl)

/-- Transporting a simple-graph edge-colouring to the associated multigraph evaluates it on the
corresponding simple edge. -/
@[simp]
theorem edgeColoringEquivOfSimpleGraph_symm_apply
    (c : G.EdgeColoring C) (e : E(Graph.ofSimpleGraph G)) :
    (edgeColoringEquivOfSimpleGraph G C).symm c e =
      c (Graph.lineGraphOfSimpleGraphIso G e) :=
  (rfl)

/-- Edge-colourability of a simple graph agrees with edge-colourability of its associated
edge-labelled multigraph. -/
theorem edgeColorableWith_iff_nonempty_edgeColoring_ofSimpleGraph :
    G.EdgeColorableWith C ↔ Nonempty ((Graph.ofSimpleGraph G).EdgeColoring C) :=
  (edgeColoringEquivOfSimpleGraph G C).nonempty_congr.symm

/-- A finite bipartite simple graph determines a displayed bipartition of its associated
edge-labelled multigraph. Vertices omitted from the initial bipartition, necessarily isolated,
are placed on its left side. -/
theorem IsBipartite.exists_isBipartition_ofSimpleGraph [Finite V]
    (hG : G.IsBipartite) :
    ∃ L R : Finset V(Graph.ofSimpleGraph G),
      (Graph.ofSimpleGraph G).IsBipartition L R := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨s, t, hst⟩ := hG.exists_isBipartiteWith
  let s' := s ∪ (s ∪ t)ᶜ
  have hst' : G.IsBipartiteWith s' t := {
    disjoint := Set.disjoint_left.2 fun x hx ht ↦ by
      rcases hx with hs | hc
      · exact Set.disjoint_left.1 hst.disjoint hs ht
      · exact hc (Or.inr ht)
    mem_of_adj := fun {_ _} hxy ↦ (hst.mem_of_adj hxy).imp
      (fun h ↦ ⟨Or.inl h.1, h.2⟩) (fun h ↦ ⟨h.1, Or.inl h.2⟩) }
  have hcover : s' ∪ t = Set.univ := by
    ext x
    simp only [s', Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    tauto
  let L : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.1 ∈ s'
  let R : Finset V(Graph.ofSimpleGraph G) := Finset.univ.filter fun x ↦ x.1 ∈ t
  have hL : Subtype.val '' (L : Set V(Graph.ofSimpleGraph G)) = s' := by
    ext x
    simp [L]
  have hR : Subtype.val '' (R : Set V(Graph.ofSimpleGraph G)) = t := by
    ext x
    simp [R]
  refine ⟨L, R, (isBipartition_ofSimpleGraph_iff G L R).2 ?_⟩
  simpa only [hL, hR] using And.intro hst' hcover

/-- **Kőnig's edge-colouring theorem.** A finite bipartite simple graph is edge-colourable by
`k` colours exactly when its maximum degree is at most `k`. -/
theorem IsBipartite.edgeColorable_iff_maxDegree_le [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsBipartite) :
    G.EdgeColorable k ↔ G.maxDegree ≤ k := by
  obtain ⟨L, R, hLR⟩ := hG.exists_isBipartition_ofSimpleGraph
  rw [show G.EdgeColorable k ↔
    Nonempty ((Graph.ofSimpleGraph G).EdgeColoring (Fin k)) from
      edgeColorableWith_iff_nonempty_edgeColoring_ofSimpleGraph]
  simpa only using nonempty_edgeColoring_ofSimpleGraph_iff_maxDegree_le G hLR

/-- **Kőnig's line-colouring theorem.** The chromatic index of a finite bipartite simple graph
is its maximum degree. Both are zero when the vertex type is empty. -/
theorem IsBipartite.chromaticIndex_eq_maxDegree [Fintype V] [DecidableRel G.Adj]
    (hG : G.IsBipartite) :
    G.chromaticIndex = G.maxDegree := by
  obtain ⟨L, R, hLR⟩ := hG.exists_isBipartition_ofSimpleGraph
  simpa only using chromaticNumber_lineGraph_eq_maxDegree G hLR

end SimpleGraph
