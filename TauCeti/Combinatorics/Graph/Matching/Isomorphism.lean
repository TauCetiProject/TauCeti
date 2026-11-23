/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Isomorphism.Basic
public import TauCeti.Combinatorics.Graph.Matching.Basic

/-!
# Isomorphism invariance of matchings

A multigraph isomorphism transports sets of actual edges by its edge equivalence. This transport
preserves and reflects matchings and perfect matchings, carries the endpoints of the selected edges
to the endpoints of their images, and restricts to an isomorphism `Graph.Iso.matchingSubgraph`
between the subgraphs of selected edges. Edge identities are part of the isomorphism, so parallel
edges and loops are treated exactly as in the original graph.

Proper edge-colourings are colourings of the line graph, so they are transported by
`SimpleGraph.coloringCongr` applied to `Graph.Iso.lineGraph`.
-/

public section

open Set
open scoped Graph

universe u v u' v'

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

namespace Iso

private theorem isMatching_image (f : Iso G H) {M : Set E(G)} (hM : G.IsMatching M) :
    H.IsMatching (f.edgeEquiv '' M) := by
  refine isMatching_def.2 ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩ x hx
    lift x to V(H) using hx.inc.vertex_mem
    exact hM.not_isLoopAt he _ ((f.map_isLoopAt_iff e (f.vertexEquiv.symm x)).1 (by simpa using hx))
  · rintro _ ⟨e, he, rfl⟩ _ ⟨g, hg, rfl⟩ hne x ⟨hex, hgx⟩
    lift x to V(H) using hex.vertex_mem
    have hex' := (f.map_inc_iff e (f.vertexEquiv.symm x)).1 (by simpa using hex)
    have hgx' := (f.map_inc_iff g (f.vertexEquiv.symm x)).1 (by simpa using hgx)
    exact hne (congrArg f.edgeEquiv (hM.eq_of_inc he hg hex' hgx'))

/-- A graph isomorphism preserves and reflects matchings. -/
@[simp]
theorem isMatching_image_iff (f : Iso G H) (M : Set E(G)) :
    H.IsMatching (f.edgeEquiv '' M) ↔ G.IsMatching M := by
  refine ⟨fun h ↦ ?_, f.isMatching_image⟩
  simpa [Equiv.symm_image_image] using f.symm.isMatching_image h

/-- A graph isomorphism preserves and reflects perfect matchings. -/
@[simp]
theorem isPerfectMatching_image_iff (f : Iso G H) (M : Set E(G)) :
    H.IsPerfectMatching (f.edgeEquiv '' M) ↔ G.IsPerfectMatching M := by
  rw [isPerfectMatching_def, isPerfectMatching_def, f.isMatching_image_iff,
    ← f.vertexEquiv.forall_congr_right]
  refine and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  simp only [exists_mem_image, map_inc_iff]

/-- An actual vertex is an endpoint of a selected edge exactly when its image is an endpoint of a
transported selected edge. -/
theorem vertexEquiv_mem_matchingSupport_image_iff (f : Iso G H) (M : Set E(G)) (x : V(G)) :
    (f.vertexEquiv x : α') ∈ H.matchingSupport (f.edgeEquiv '' M) ↔
      (x : α) ∈ G.matchingSupport M := by
  simp only [mem_matchingSupport, exists_mem_image, map_inc_iff]

/-- A graph isomorphism carries the endpoints of the selected edges to the endpoints of their
images. -/
@[simp]
theorem mapVertexSet_matchingSupport (f : Iso G H) (M : Set E(G)) :
    f.mapVertexSet (G.matchingSupport M) = H.matchingSupport (f.edgeEquiv '' M) := by
  ext y
  by_cases hy : y ∈ V(H)
  · lift y to V(H) using hy
    rw [f.mem_mapVertexSet_iff, ← f.vertexEquiv_mem_matchingSupport_image_iff,
      Equiv.apply_symm_apply]
  · exact iff_of_false (fun h ↦ hy (f.mapVertexSet_subset_vertexSet _ h))
      (fun h ↦ hy (matchingSupport_subset_vertexSet h))

private theorem mem_of_mem_edgeSet_matchingSubgraph {M : Set E(G)} {e : β}
    (he : e ∈ E(G.matchingSubgraph M)) :
    (⟨e, (G.matchingSubgraph_le M).edgeSet_mono he⟩ : E(G)) ∈ M := by
  have h := he
  rw [edgeSet_matchingSubgraph] at h
  obtain ⟨e', he', rfl⟩ := h
  exact he'

/-- A graph isomorphism restricts to an isomorphism between the subgraphs of selected edges. -/
def matchingSubgraph (f : Iso G H) (M : Set E(G)) :
    Iso (G.matchingSubgraph M) (H.matchingSubgraph (f.edgeEquiv '' M)) where
  vertexEquiv :=
    { toFun x := ⟨f.vertexEquiv ⟨x, (G.matchingSubgraph_le M).vertexSet_mono x.property⟩, by
        rw [vertexSet_matchingSubgraph, f.vertexEquiv_mem_matchingSupport_image_iff]
        simpa only [vertexSet_matchingSubgraph] using x.property⟩
      invFun y := ⟨f.vertexEquiv.symm ⟨y, (H.matchingSubgraph_le _).vertexSet_mono y.property⟩, by
        rw [vertexSet_matchingSubgraph, ← f.vertexEquiv_mem_matchingSupport_image_iff,
          Equiv.apply_symm_apply]
        simpa only [vertexSet_matchingSubgraph] using y.property⟩
      left_inv x := by simp
      right_inv y := by simp }
  edgeEquiv :=
    { toFun e := ⟨f.edgeEquiv ⟨e, (G.matchingSubgraph_le M).edgeSet_mono e.property⟩, by
        rw [edgeSet_matchingSubgraph]
        exact ⟨_, ⟨_, mem_of_mem_edgeSet_matchingSubgraph e.property, rfl⟩, rfl⟩⟩
      invFun e := ⟨f.edgeEquiv.symm ⟨e, (H.matchingSubgraph_le _).edgeSet_mono e.property⟩, by
        obtain ⟨e', he', hee⟩ := mem_of_mem_edgeSet_matchingSubgraph e.property
        rw [edgeSet_matchingSubgraph]
        refine ⟨e', he', ?_⟩
        rw [← hee, Equiv.symm_apply_apply]⟩
      left_inv e := by simp
      right_inv e := by simp }
  map_isLink_iff e x y := by
    have heM := mem_of_mem_edgeSet_matchingSubgraph e.property
    have hx := (G.matchingSubgraph_le M).vertexSet_mono x.property
    have hy := (G.matchingSubgraph_le M).vertexSet_mono y.property
    have hlink := f.map_isLink_iff ⟨e, (G.matchingSubgraph_le M).edgeSet_mono e.property⟩ ⟨x, hx⟩
        ⟨y, hy⟩
    simp only [Equiv.coe_fn_mk, matchingSubgraph_isLink]
    constructor
    · rintro ⟨-, -, h⟩
      exact ⟨_, heM, hlink.1 h⟩
    · rintro ⟨-, -, h⟩
      exact ⟨(f.edgeEquiv _).property, ⟨_, heM, rfl⟩, hlink.2 h⟩

/-- The vertex equivalence of `Graph.Iso.matchingSubgraph` is the vertex equivalence of the
ambient isomorphism. -/
@[simp]
theorem coe_matchingSubgraph_vertexEquiv_apply (f : Iso G H) (M : Set E(G))
    (x : V(G.matchingSubgraph M)) :
    ((f.matchingSubgraph M).vertexEquiv x : α') =
      f.vertexEquiv ⟨x, (G.matchingSubgraph_le M).vertexSet_mono x.property⟩ :=
  (rfl)

/-- The inverse vertex equivalence of `Graph.Iso.matchingSubgraph` is the inverse vertex
equivalence of the ambient isomorphism. -/
@[simp]
theorem coe_matchingSubgraph_vertexEquiv_symm_apply (f : Iso G H) (M : Set E(G))
    (y : V(H.matchingSubgraph (f.edgeEquiv '' M))) :
    ((f.matchingSubgraph M).vertexEquiv.symm y : α) =
      f.vertexEquiv.symm ⟨y, (H.matchingSubgraph_le _).vertexSet_mono y.property⟩ :=
  (rfl)

/-- The edge equivalence of `Graph.Iso.matchingSubgraph` is the edge equivalence of the ambient
isomorphism. -/
@[simp]
theorem coe_matchingSubgraph_edgeEquiv_apply (f : Iso G H) (M : Set E(G))
    (e : E(G.matchingSubgraph M)) :
    ((f.matchingSubgraph M).edgeEquiv e : β') =
      f.edgeEquiv ⟨e, (G.matchingSubgraph_le M).edgeSet_mono e.property⟩ :=
  (rfl)

/-- The inverse edge equivalence of `Graph.Iso.matchingSubgraph` is the inverse edge equivalence
of the ambient isomorphism. -/
@[simp]
theorem coe_matchingSubgraph_edgeEquiv_symm_apply (f : Iso G H) (M : Set E(G))
    (e : E(H.matchingSubgraph (f.edgeEquiv '' M))) :
    ((f.matchingSubgraph M).edgeEquiv.symm e : β) =
      f.edgeEquiv.symm ⟨e, (H.matchingSubgraph_le _).edgeSet_mono e.property⟩ :=
  (rfl)

end Iso

end Graph
