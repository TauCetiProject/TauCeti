/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.EdgeEnds
public import TauCeti.Combinatorics.Graph.Isomorphism

/-!
# Simple multigraphs and their underlying simple graphs

A simple multigraph has no loops and at most one edge between any two vertices. Consequently,
its actual edges are canonically equivalent to the edges of its underlying `SimpleGraph`, by
sending an edge to its unordered pair of ends.

This edge equivalence combines with the identity equivalence on actual vertices to identify a
simple multigraph `G` with `Graph.ofSimpleGraph G.toSimpleGraph`. It supplies the reverse of
Mathlib's `Graph.toSimpleGraphOfSimpleGraphIso`, so the two graph representations can be used
interchangeably when edge identities carry no additional information.

## Main declarations

* `Graph.edgeEndsEquiv`: actual edges of a simple multigraph are the edges of its underlying
  simple graph.
* `Graph.ofSimpleGraphEdgeSetEquiv`: actual edges of the multigraph built from a simple graph
  are the edges of that simple graph.
* `Graph.ofSimpleGraphToSimpleGraphIso`: the canonical multigraph isomorphism from the graph
  reconstructed from the underlying simple graph to the original simple multigraph.
-/

public section

open Set

universe u v

namespace Graph

variable {V : Type u} {E : Type v} {G : Graph V E}

private theorem edgeEnds_mem_toSimpleGraph_edgeSet [G.Simple] (e : G.edgeSet) :
    G.edgeEnds e ∈ G.toSimpleGraph.edgeSet := by
  rw [← Sym2.mk_fst_out_snd_out (G.edgeEnds e), SimpleGraph.mem_edgeSet,
    G.toSimpleGraph_adj_iff]
  exact ((G.edgeEnds_eq_iff_isLink e _ _).1
    (Sym2.mk_fst_out_snd_out (G.edgeEnds e)).symm).adj

private theorem edgeEnds_injective [G.Simple] : Function.Injective G.edgeEnds := by
  intro e f hef
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  let x' : G.vertexSet := ⟨x, hxy.left_mem⟩
  let y' : G.vertexSet := ⟨y, hxy.right_mem⟩
  have he : G.edgeEnds e = s(x', y') := (G.edgeEnds_eq_iff_isLink e x' y').2 hxy
  have hf : G.edgeEnds f = s(x', y') := hef.symm.trans he
  exact Subtype.ext (hxy.eq ((G.edgeEnds_eq_iff_isLink f x' y').1 hf))

private theorem edgeEnds_surjective [G.Simple] :
    Function.Surjective fun e : G.edgeSet ↦
      (⟨G.edgeEnds e, edgeEnds_mem_toSimpleGraph_edgeSet e⟩ : G.toSimpleGraph.edgeSet) := by
  intro p
  let x := p.1.out.1
  let y := p.1.out.2
  have hadj : G.toSimpleGraph.Adj x y := by
    rw [← SimpleGraph.mem_edgeSet, Sym2.mk_fst_out_snd_out]
    exact p.2
  obtain ⟨e, he⟩ := (G.toSimpleGraph_adj_iff x y).1 hadj
  let e' : G.edgeSet := ⟨e, he.edge_mem⟩
  refine ⟨e', Subtype.ext ?_⟩
  exact ((G.edgeEnds_eq_iff_isLink e' x y).2 he).trans
    (Sym2.mk_fst_out_snd_out p.1)

/-- The actual edges of a simple multigraph are canonically equivalent to the edges of its
underlying simple graph. The equivalence sends each edge identity to its unordered pair of ends.
-/
noncomputable def edgeEndsEquiv (G : Graph V E) [G.Simple] :
    G.edgeSet ≃ G.toSimpleGraph.edgeSet :=
  Equiv.ofBijective
    (fun e ↦ ⟨G.edgeEnds e, edgeEnds_mem_toSimpleGraph_edgeSet e⟩)
    ⟨fun _ _ h ↦ edgeEnds_injective (Subtype.ext_iff.mp h), edgeEnds_surjective⟩

/-- The edge equivalence from a simple multigraph to its underlying simple graph is given by
`Graph.edgeEnds`. -/
@[simp]
theorem coe_edgeEndsEquiv_apply (G : Graph V E) [G.Simple] (e : G.edgeSet) :
    (G.edgeEndsEquiv e : Sym2 G.vertexSet) = G.edgeEnds e :=
  (rfl)

/-- The edge selected by the inverse endpoint equivalence has the prescribed unordered ends. -/
@[simp]
theorem edgeEnds_edgeEndsEquiv_symm_apply (G : Graph V E) [G.Simple]
    (p : G.toSimpleGraph.edgeSet) :
    G.edgeEnds (G.edgeEndsEquiv.symm p) = p := by
  exact congrArg Subtype.val (G.edgeEndsEquiv.apply_symm_apply p)

/-- The actual edges of the multigraph built from a simple graph are exactly the edges of that
simple graph. -/
def ofSimpleGraphEdgeSetEquiv {α : Type*} (H : SimpleGraph α) :
    (ofSimpleGraph H).edgeSet ≃ H.edgeSet :=
  Equiv.subtypeEquivRight fun _ ↦ by rw [edgeSet_ofSimpleGraph]

/-- The edge equivalence `Graph.ofSimpleGraphEdgeSetEquiv` does not change the underlying
unordered pair. -/
@[simp]
theorem coe_ofSimpleGraphEdgeSetEquiv_apply {α : Type*} (H : SimpleGraph α)
    (e : (ofSimpleGraph H).edgeSet) :
    (ofSimpleGraphEdgeSetEquiv H e : Sym2 α) = e :=
  (rfl)

/-- The inverse of `Graph.ofSimpleGraphEdgeSetEquiv` does not change the underlying unordered
pair. -/
@[simp]
theorem coe_ofSimpleGraphEdgeSetEquiv_symm_apply {α : Type*} (H : SimpleGraph α)
    (e : H.edgeSet) :
    ((ofSimpleGraphEdgeSetEquiv H).symm e : Sym2 α) = e :=
  (rfl)

/-- Reconstructing a simple multigraph from its underlying simple graph gives an isomorphic
multigraph. The isomorphism fixes actual vertices and identifies an unordered pair of adjacent
vertices with the unique original edge having those ends. -/
noncomputable def ofSimpleGraphToSimpleGraphIso (G : Graph V E) [G.Simple] :
    Iso (ofSimpleGraph G.toSimpleGraph) G where
  vertexEquiv := Equiv.Set.univ G.vertexSet
  edgeEquiv := (ofSimpleGraphEdgeSetEquiv G.toSimpleGraph).trans G.edgeEndsEquiv.symm
  map_isLink_iff e x y := by
    simp only [Equiv.trans_apply]
    rw [← G.edgeEnds_eq_iff_isLink, G.edgeEnds_edgeEndsEquiv_symm_apply]
    simp only [ofSimpleGraph_isLink, coe_ofSimpleGraphEdgeSetEquiv_apply]
    constructor
    · intro h
      exact ⟨h, by simpa only [edgeSet_ofSimpleGraph] using e.2⟩
    · exact fun h ↦ h.1

/-- The reverse simple-graph round-trip isomorphism fixes each actual vertex. -/
@[simp]
theorem ofSimpleGraphToSimpleGraphIso_vertexEquiv_apply (G : Graph V E) [G.Simple]
    (x : (ofSimpleGraph G.toSimpleGraph).vertexSet) :
    (G.ofSimpleGraphToSimpleGraphIso.vertexEquiv x : V) = (x.1 : G.vertexSet) :=
  (rfl)

/-- The original edge corresponding to an edge of the reconstructed graph has exactly the
displayed unordered pair of ends. -/
@[simp]
theorem edgeEnds_ofSimpleGraphToSimpleGraphIso_edgeEquiv_apply
    (G : Graph V E) [G.Simple] (e : (ofSimpleGraph G.toSimpleGraph).edgeSet) :
    G.edgeEnds (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv e) = e :=
  G.edgeEnds_edgeEndsEquiv_symm_apply (ofSimpleGraphEdgeSetEquiv G.toSimpleGraph e)

/-- In the inverse round-trip isomorphism, an original edge is sent to its unordered pair of
ends. -/
@[simp]
theorem coe_ofSimpleGraphToSimpleGraphIso_symm_edgeEquiv_apply
    (G : Graph V E) [G.Simple] (e : G.edgeSet) :
    (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv.symm e : Sym2 G.vertexSet) = G.edgeEnds e := by
  have h := G.edgeEnds_ofSimpleGraphToSimpleGraphIso_edgeEquiv_apply
    (G.ofSimpleGraphToSimpleGraphIso.edgeEquiv.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end Graph
