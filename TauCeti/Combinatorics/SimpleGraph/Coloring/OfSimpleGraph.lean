/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Coloring
public import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph

/-!
# Colour-class and matching-partition transport for `Graph.ofSimpleGraph`

For a simple graph `H`, `SimpleGraph.edgeColoringEquivOfSimpleGraph H C` identifies proper
edge-colourings of `H` with proper multigraph edge-colourings of `Graph.ofSimpleGraph H`, while
`SimpleGraph.matchingEquiv H` identifies multigraph matchings of `Graph.ofSimpleGraph H` with
matching subgraphs of `H`.

This file proves that these two correspondences commute:

* `SimpleGraph.colorClass_edgeColoringEquivOfSimpleGraph` and
  `SimpleGraph.colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm` show that colour classes
  correspond via `SimpleGraph.Subgraph.toGraphEdgeSet` and `SimpleGraph.matchingSubgraph`;
* `SimpleGraph.matchingEquiv_colorClass` and `SimpleGraph.matchingEquiv_symm_colorClassSubgraph`
  express this compatibility directly through `SimpleGraph.matchingEquiv`;
* `SimpleGraph.edgeColoringEquivOfSimpleGraph_ofMatchings` and
  `SimpleGraph.edgeColoringEquivOfSimpleGraph_symm_ofMatchings` show that building an edge-colouring
  from an indexed partition into matchings commutes with
  `SimpleGraph.edgeColoringEquivOfSimpleGraph` in both directions.
-/

public section

open Set
open scoped Graph

universe u w

namespace SimpleGraph

variable {V : Type u} {C : Type w} {H : SimpleGraph V}

/-- The `i`-th colour class of `H.edgeColoringEquivOfSimpleGraph C c` is the set of actual edges
selected by `c.colorClassSubgraph i`. -/
@[simp]
theorem colorClass_edgeColoringEquivOfSimpleGraph (c : H.EdgeColoring C) (i : C) :
    (H.edgeColoringEquivOfSimpleGraph C c).colorClass i =
      (c.colorClassSubgraph i).toGraphEdgeSet := by
  ext e
  rw [Subgraph.mem_toGraphEdgeSet, EdgeColoring.edgeSet_colorClassSubgraph]
  simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_apply]
  constructor
  · intro he
    exact ⟨Graph.lineGraphOfSimpleGraphIso H e, he, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩
  · rintro ⟨e', he', hee'⟩
    have heq : Graph.lineGraphOfSimpleGraphIso H e = e' :=
      Subtype.ext ((Graph.coe_lineGraphOfSimpleGraphIso_apply H e).trans hee'.symm)
    exact (congrArg c heq).trans he'

/-- Transporting a multigraph edge-colouring of `Graph.ofSimpleGraph H` back to `H` sends its
`i`-th colour class to `H.matchingSubgraph (c.colorClass i)`. -/
@[simp]
theorem colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm
    (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    ((H.edgeColoringEquivOfSimpleGraph C).symm c).colorClassSubgraph i =
      H.matchingSubgraph (c.colorClass i) := by
  refine Subgraph.IsMatching.injOn_edgeSet
    (((H.edgeColoringEquivOfSimpleGraph C).symm c).isMatching_colorClassSubgraph i)
    ((H.matchingSubgraph_isMatching_iff (c.colorClass i)).2 (c.isMatching_colorClass i)) ?_
  ext p
  rw [EdgeColoring.edgeSet_colorClassSubgraph, edgeSet_matchingSubgraph]
  constructor
  · rintro ⟨e, he, rfl⟩
    simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_symm_apply] at he
    exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e, he,
      Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨Graph.lineGraphOfSimpleGraphIso H e, ?_, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩
    simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_symm_apply,
      RelIso.symm_apply_apply]
    exact he

/-- Under `SimpleGraph.matchingEquiv`, the `i`-th colour class of a multigraph edge-colouring `c`
maps to the `i`-th colour-class subgraph of `(H.edgeColoringEquivOfSimpleGraph C).symm c`. -/
theorem matchingEquiv_colorClass (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    H.matchingEquiv ⟨c.colorClass i, c.isMatching_colorClass i⟩ =
      ⟨((H.edgeColoringEquivOfSimpleGraph C).symm c).colorClassSubgraph i,
        ((H.edgeColoringEquivOfSimpleGraph C).symm c).isMatching_colorClassSubgraph i⟩ :=
  Subtype.ext ((H.matchingEquiv_apply _).trans
    (colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm c i).symm)

/-- Under `(SimpleGraph.matchingEquiv H).symm`, the `i`-th colour-class subgraph of a simple-graph
edge-colouring `c` maps to the `i`-th colour class of `H.edgeColoringEquivOfSimpleGraph C c`. -/
theorem matchingEquiv_symm_colorClassSubgraph (c : H.EdgeColoring C) (i : C) :
    (H.matchingEquiv).symm ⟨c.colorClassSubgraph i, c.isMatching_colorClassSubgraph i⟩ =
      ⟨(H.edgeColoringEquivOfSimpleGraph C c).colorClass i,
        (H.edgeColoringEquivOfSimpleGraph C c).isMatching_colorClass i⟩ :=
  Subtype.ext ((H.matchingEquiv_symm_apply _).trans
    (colorClass_edgeColoringEquivOfSimpleGraph c i).symm)

/-- Transporting `SimpleGraph.EdgeColoring.ofMatchings` along
`SimpleGraph.edgeColoringEquivOfSimpleGraph` agrees with `Graph.EdgeColoring.ofMatchings` on the
selected actual edge sets. -/
theorem edgeColoringEquivOfSimpleGraph_ofMatchings
    (M : C → H.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : H.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet)
    (hpart' : ∀ e : E(Graph.ofSimpleGraph H), ∃! i, e ∈ (M i).toGraphEdgeSet) :
    H.edgeColoringEquivOfSimpleGraph C (EdgeColoring.ofMatchings M hM hpart) =
      Graph.EdgeColoring.ofMatchings (fun i ↦ (M i).toGraphEdgeSet)
        (fun i ↦ by
          rw [← H.matchingSubgraph_isMatching_iff, (M i).matchingSubgraph_toGraphEdgeSet (hM i)]
          exact hM i) hpart' := by
  ext e
  symm
  rw [Graph.EdgeColoring.ofMatchings_apply_eq_iff, edgeColoringEquivOfSimpleGraph_apply,
    Subgraph.mem_toGraphEdgeSet, ← Graph.coe_lineGraphOfSimpleGraphIso_apply H e]
  exact (EdgeColoring.ofMatchings_apply_eq_iff M hM hpart _ _).1 rfl

/-- Transporting `Graph.EdgeColoring.ofMatchings` along
`(SimpleGraph.edgeColoringEquivOfSimpleGraph H C).symm` agrees with
`SimpleGraph.EdgeColoring.ofMatchings` on the traced matching subgraphs. -/
theorem edgeColoringEquivOfSimpleGraph_symm_ofMatchings
    (M : C → Set E(Graph.ofSimpleGraph H))
    (hM : ∀ i, (Graph.ofSimpleGraph H).IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i)
    (hpart' : ∀ e : H.edgeSet, ∃! i, (e : Sym2 V) ∈ (H.matchingSubgraph (M i)).edgeSet) :
    (H.edgeColoringEquivOfSimpleGraph C).symm (Graph.EdgeColoring.ofMatchings M hM hpart) =
      EdgeColoring.ofMatchings (fun i ↦ H.matchingSubgraph (M i))
        (fun i ↦ (H.matchingSubgraph_isMatching_iff (M i)).2 (hM i)) hpart' := by
  ext e
  symm
  rw [EdgeColoring.ofMatchings_apply_eq_iff, edgeColoringEquivOfSimpleGraph_symm_apply,
    edgeSet_matchingSubgraph]
  exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e,
    (Graph.EdgeColoring.ofMatchings_apply_eq_iff M hM hpart _ _).1 rfl,
    Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩

end SimpleGraph
