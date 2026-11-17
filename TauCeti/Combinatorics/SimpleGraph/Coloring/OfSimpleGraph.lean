/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Matching.Coloring
public import TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.SimpleGraph.Coloring.Edge

/-!
# Edge-colouring transport between simple graphs and multigraphs

For a simple graph `H`, the multigraph `Graph.ofSimpleGraph H` has the unordered pairs in
`H.edgeSet` as its actual edge identities, and `Graph.lineGraphOfSimpleGraphIso H` identifies its
multigraph line graph with `H.lineGraph`. Conversely, for a simple multigraph `G` (`[G.Simple]`),
`Graph.ofSimpleGraphToSimpleGraphIso` identifies `Graph.ofSimpleGraph G.toSimpleGraph` with `G`.

This file transports proper edge-colourings, colour-class matchings, `EdgeColorable`, and
`chromaticIndex` across both identifications:

* `SimpleGraph.ofSimpleGraphEdgeColoringEquiv H C` identifies multigraph edge-colourings of
  `Graph.ofSimpleGraph H` with simple-graph edge-colourings of `H`, intertwining colour classes
  with `SimpleGraph.matchingSubgraph`, `SimpleGraph.Subgraph.toGraphEdgeSet`, and
  `SimpleGraph.matchingEquiv`;
* `Graph.toSimpleGraphEdgeColoringEquiv G C` identifies multigraph edge-colourings of a simple
  multigraph `G` with edge-colourings of its underlying simple graph `G.toSimpleGraph`.

## Main definitions

* `SimpleGraph.ofSimpleGraphEdgeColoringEquiv`: equivalence
  `(Graph.ofSimpleGraph H).EdgeColoring C ≃ H.EdgeColoring C`.
* `Graph.lineGraphToSimpleGraphIso` and `Graph.toSimpleGraphEdgeColoringEquiv`: line-graph
  isomorphism and edge-colouring equivalence between a simple multigraph `G` and `G.toSimpleGraph`.

## Main results

* `SimpleGraph.colorClassSubgraph_ofSimpleGraphEdgeColoringEquiv` and
  `SimpleGraph.toGraphEdgeSet_colorClassSubgraph`: colour classes correspond under
  `SimpleGraph.matchingSubgraph` and `SimpleGraph.Subgraph.toGraphEdgeSet`.
* `SimpleGraph.ofSimpleGraphEdgeColoringEquiv_ofMatchings`: matching-partition constructions of
  edge-colourings commute with the transport.
* `SimpleGraph.edgeColorable_iff_nonempty_ofSimpleGraph_edgeColoring` and
  `SimpleGraph.chromaticNumber_lineGraph_ofSimpleGraph_eq_chromaticIndex`: `EdgeColorable` and
  `chromaticIndex` agree with the multigraph line-graph formulations on `Graph.ofSimpleGraph H`.
* `Graph.chromaticNumber_lineGraph_eq_toSimpleGraph_chromaticIndex`: the chromatic number of the
  line graph of a simple multigraph equals `G.toSimpleGraph.chromaticIndex`.
-/

public section

open Set
open scoped Graph

universe u v w

namespace SimpleGraph

variable {V : Type u} {C : Type w} {H : SimpleGraph V}

/-- Equivalence between proper multigraph edge-colourings of `Graph.ofSimpleGraph H` and proper
edge-colourings of the simple graph `H`. -/
def ofSimpleGraphEdgeColoringEquiv (H : SimpleGraph V) (C : Type w) :
    (Graph.ofSimpleGraph H).EdgeColoring C ≃ H.EdgeColoring C :=
  coloringCongr (Graph.lineGraphOfSimpleGraphIso H) (.refl C)

/-- Evaluating `H.ofSimpleGraphEdgeColoringEquiv C c` on an edge of `H` looks up the corresponding
actual edge of `Graph.ofSimpleGraph H`. -/
@[simp]
theorem ofSimpleGraphEdgeColoringEquiv_apply (c : (Graph.ofSimpleGraph H).EdgeColoring C)
    (e : H.edgeSet) :
    H.ofSimpleGraphEdgeColoringEquiv C c e = c ((Graph.lineGraphOfSimpleGraphIso H).symm e) :=
  (rfl)

/-- Evaluating `(H.ofSimpleGraphEdgeColoringEquiv C).symm c` on an actual edge of
`Graph.ofSimpleGraph H` looks up the corresponding edge of `H`. -/
@[simp]
theorem ofSimpleGraphEdgeColoringEquiv_symm_apply (c : H.EdgeColoring C)
    (e : E(Graph.ofSimpleGraph H)) :
    (H.ofSimpleGraphEdgeColoringEquiv C).symm c e = c (Graph.lineGraphOfSimpleGraphIso H e) :=
  (rfl)

/-- Transporting a multigraph edge-colouring of `Graph.ofSimpleGraph H` to `H` sends its `i`-th
colour class to `H.matchingSubgraph (c.colorClass i)`. -/
@[simp]
theorem colorClassSubgraph_ofSimpleGraphEdgeColoringEquiv
    (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    (H.ofSimpleGraphEdgeColoringEquiv C c).colorClassSubgraph i =
      H.matchingSubgraph (c.colorClass i) := by
  refine Subgraph.IsMatching.injOn_edgeSet
    ((H.ofSimpleGraphEdgeColoringEquiv C c).isMatching_colorClassSubgraph i)
    ((H.matchingSubgraph_isMatching_iff (c.colorClass i)).2 (c.isMatching_colorClass i)) ?_
  ext p
  rw [EdgeColoring.edgeSet_colorClassSubgraph, edgeSet_matchingSubgraph]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e, he,
      Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨Graph.lineGraphOfSimpleGraphIso H e, ?_, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩
    simp only [Coloring.colorClass, mem_ofPred_eq, ofSimpleGraphEdgeColoringEquiv_apply,
      RelIso.symm_apply_apply]
    exact he

/-- Converting `(c.colorClassSubgraph i).toGraphEdgeSet` recovers the `i`-th colour class of the
transported multigraph edge-colouring. -/
@[simp]
theorem toGraphEdgeSet_colorClassSubgraph (c : H.EdgeColoring C) (i : C) :
    (c.colorClassSubgraph i).toGraphEdgeSet =
      ((H.ofSimpleGraphEdgeColoringEquiv C).symm c).colorClass i := by
  ext e
  rw [Subgraph.mem_toGraphEdgeSet, EdgeColoring.edgeSet_colorClassSubgraph]
  simp only [Coloring.colorClass, mem_ofPred_eq, ofSimpleGraphEdgeColoringEquiv_symm_apply]
  constructor
  · rintro ⟨e', he', hee'⟩
    have heq : Graph.lineGraphOfSimpleGraphIso H e = e' :=
      Subtype.ext ((Graph.coe_lineGraphOfSimpleGraphIso_apply H e).trans hee'.symm)
    exact (congrArg c heq).trans he'
  · intro he
    exact ⟨Graph.lineGraphOfSimpleGraphIso H e, he, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩

/-- Under `SimpleGraph.matchingEquiv`, the `i`-th colour class of a multigraph edge-colouring `c`
maps to the `i`-th colour-class subgraph of `H.ofSimpleGraphEdgeColoringEquiv C c`. -/
theorem matchingEquiv_colorClass (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    H.matchingEquiv ⟨c.colorClass i, c.isMatching_colorClass i⟩ =
      ⟨(H.ofSimpleGraphEdgeColoringEquiv C c).colorClassSubgraph i,
        (H.ofSimpleGraphEdgeColoringEquiv C c).isMatching_colorClassSubgraph i⟩ :=
  Subtype.ext ((H.matchingEquiv_apply _).trans
    (colorClassSubgraph_ofSimpleGraphEdgeColoringEquiv c i).symm)

/-- Transporting `Graph.EdgeColoring.ofMatchings` along `H.ofSimpleGraphEdgeColoringEquiv C` agrees
with `SimpleGraph.EdgeColoring.ofMatchings` on the traced matching subgraphs. -/
theorem ofSimpleGraphEdgeColoringEquiv_ofMatchings
    (M : C → Set E(Graph.ofSimpleGraph H))
    (hM : ∀ i, (Graph.ofSimpleGraph H).IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i)
    (hpart' : ∀ e : H.edgeSet, ∃! i, (e : Sym2 V) ∈ (H.matchingSubgraph (M i)).edgeSet) :
    H.ofSimpleGraphEdgeColoringEquiv C (Graph.EdgeColoring.ofMatchings M hM hpart) =
      EdgeColoring.ofMatchings (fun i ↦ H.matchingSubgraph (M i))
        (fun i ↦ (H.matchingSubgraph_isMatching_iff (M i)).2 (hM i)) hpart' := by
  ext e
  symm
  rw [EdgeColoring.ofMatchings_apply_eq_iff, ofSimpleGraphEdgeColoringEquiv_apply,
    edgeSet_matchingSubgraph]
  exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e,
    (Graph.EdgeColoring.ofMatchings_apply_eq_iff M hM hpart _ _).1 rfl,
    Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩

/-- `H` is `n`-edge-colourable iff `Graph.ofSimpleGraph H` admits a proper edge-colouring by
`Fin n`. -/
theorem edgeColorable_iff_nonempty_ofSimpleGraph_edgeColoring {n : ℕ} :
    H.EdgeColorable n ↔ Nonempty ((Graph.ofSimpleGraph H).EdgeColoring (Fin n)) :=
  H.edgeColorable_def.trans (H.ofSimpleGraphEdgeColoringEquiv (Fin n)).symm.nonempty_congr

/-- The chromatic number of `(Graph.ofSimpleGraph H).lineGraph` equals `H.chromaticIndex`. -/
@[simp]
theorem chromaticNumber_lineGraph_ofSimpleGraph_eq_chromaticIndex (H : SimpleGraph V) :
    (Graph.ofSimpleGraph H).lineGraph.chromaticNumber = H.chromaticIndex :=
  (Graph.chromaticNumber_lineGraph_ofSimpleGraph H).trans
    H.chromaticIndex_eq_chromaticNumber_lineGraph.symm

end SimpleGraph

namespace Graph

variable {V : Type u} {E : Type v} {C : Type w} {G : Graph V E}

/-- For a simple multigraph `G`, its line graph is isomorphic to the line graph of its underlying
simple graph `G.toSimpleGraph`. -/
noncomputable def lineGraphToSimpleGraphIso (G : Graph V E) [G.Simple] :
    G.lineGraph ≃g G.toSimpleGraph.lineGraph :=
  G.ofSimpleGraphToSimpleGraphIso.symm.lineGraph.trans (lineGraphOfSimpleGraphIso G.toSimpleGraph)

/-- Evaluating `Graph.lineGraphToSimpleGraphIso` sends each actual edge of `G` to its unordered
pair of endpoints in `G.toSimpleGraph.edgeSet`. -/
@[simp]
theorem coe_lineGraphToSimpleGraphIso_apply (G : Graph V E) [G.Simple] (e : E(G)) :
    (G.lineGraphToSimpleGraphIso e : Sym2 V(G)) = G.edgeEnds e := by
  simp [lineGraphToSimpleGraphIso]

/-- Equivalence between proper multigraph edge-colourings of a simple multigraph `G` and proper
edge-colourings of its underlying simple graph `G.toSimpleGraph`. -/
noncomputable def toSimpleGraphEdgeColoringEquiv (G : Graph V E) [G.Simple] (C : Type w) :
    G.EdgeColoring C ≃ G.toSimpleGraph.EdgeColoring C :=
  SimpleGraph.coloringCongr G.lineGraphToSimpleGraphIso (.refl C)

/-- Evaluating `G.toSimpleGraphEdgeColoringEquiv C c` on an edge of `G.toSimpleGraph` looks up the
corresponding actual edge of `G`. -/
@[simp]
theorem toSimpleGraphEdgeColoringEquiv_apply [G.Simple]
    (c : G.EdgeColoring C) (e : G.toSimpleGraph.edgeSet) :
    G.toSimpleGraphEdgeColoringEquiv C c e = c (G.lineGraphToSimpleGraphIso.symm e) :=
  (rfl)

/-- Evaluating `(G.toSimpleGraphEdgeColoringEquiv C).symm c` on an actual edge `e` looks up the
colour of its endpoint pair in `G.toSimpleGraph`. -/
@[simp]
theorem toSimpleGraphEdgeColoringEquiv_symm_apply [G.Simple]
    (c : G.toSimpleGraph.EdgeColoring C) (e : E(G)) :
    (G.toSimpleGraphEdgeColoringEquiv C).symm c e = c (G.lineGraphToSimpleGraphIso e) :=
  (rfl)

/-- A simple multigraph `G` admits a proper edge-colouring by `Fin n` iff `G.toSimpleGraph` is
`n`-edge-colourable. -/
theorem nonempty_edgeColoring_iff_toSimpleGraph_edgeColorable [G.Simple] {n : ℕ} :
    Nonempty (G.EdgeColoring (Fin n)) ↔ G.toSimpleGraph.EdgeColorable n :=
  (G.toSimpleGraphEdgeColoringEquiv (Fin n)).nonempty_congr.trans
    G.toSimpleGraph.edgeColorable_def.symm

/-- For a simple multigraph `G`, the chromatic number of `G.lineGraph` equals
`G.toSimpleGraph.chromaticIndex`. -/
theorem chromaticNumber_lineGraph_eq_toSimpleGraph_chromaticIndex (G : Graph V E) [G.Simple] :
    G.lineGraph.chromaticNumber = G.toSimpleGraph.chromaticIndex :=
  (SimpleGraph.chromaticNumber_congr G.lineGraphToSimpleGraphIso).trans
    G.toSimpleGraph.chromaticIndex_eq_chromaticNumber_lineGraph.symm

end Graph
