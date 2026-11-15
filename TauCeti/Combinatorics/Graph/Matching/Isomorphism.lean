/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Isomorphism
public import TauCeti.Combinatorics.Graph.Matching.Capacitated
public import TauCeti.Combinatorics.Graph.Regular

/-!
# Isomorphism invariance of matchings, vertex covers and bipartitions

A multigraph isomorphism transports sets of actual edges and actual vertices by its two
equivalences. This transport preserves and reflects matchings, perfect matchings, vertex covers
and bipartitions. Pulling vertex capacities and edge multiplicities back along the isomorphism
preserves and reflects multiset capacitated matchings, and isomorphic multigraphs are regular of
the same degree. Edge identities are part of the isomorphism, so parallel edges and loops are
treated exactly as in the original graph.

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

/-- A graph isomorphism preserves and reflects vertex covers. -/
@[simp]
theorem isVertexCover_image_iff (f : Iso G H) (C : Set V(G)) :
    H.IsVertexCover (f.vertexEquiv '' C) ↔ G.IsVertexCover C := by
  rw [isVertexCover_iff_forall_exists_inc, isVertexCover_iff_forall_exists_inc,
    ← f.edgeEquiv.forall_congr_right]
  refine forall_congr' fun e ↦ ?_
  simp only [exists_mem_image, map_inc_iff]

private theorem isBipartition_map (f : Iso G H) {L R : Finset V(G)} (h : G.IsBipartition L R) :
    H.IsBipartition (L.map f.vertexEquiv.toEmbedding) (R.map f.vertexEquiv.toEmbedding) where
  disjoint := (Finset.disjoint_map _).2 h.disjoint
  mem_or_mem x := by simpa only [Finset.mem_map_equiv] using h.mem_or_mem (f.vertexEquiv.symm x)
  isLink {e x y} he := by
    simp only [Finset.mem_map_equiv]
    exact h.isLink
      ((f.map_isLink_iff (f.edgeEquiv.symm ⟨e, he.edge_mem⟩) _ _).1 (by simpa using he))

/-- A graph isomorphism preserves and reflects bipartitions. -/
@[simp]
theorem isBipartition_map_iff (f : Iso G H) (L R : Finset V(G)) :
    H.IsBipartition (L.map f.vertexEquiv.toEmbedding) (R.map f.vertexEquiv.toEmbedding) ↔
      G.IsBipartition L R := by
  refine ⟨fun h ↦ ?_, f.isBipartition_map⟩
  simpa [Finset.map_map] using f.symm.isBipartition_map h

/-- Pulling vertex capacities and edge multiplicities back along a graph isomorphism preserves
and reflects multiset capacitated matchings. -/
@[simp]
theorem isCapacitatedMatching_comp_iff [Fintype E(G)] [Fintype E(H)] (f : Iso G H)
    (b : V(H) → ℕ) (x : E(H) → ℕ) :
    G.IsCapacitatedMatching (b ∘ f.vertexEquiv) (x ∘ f.edgeEquiv) ↔
      H.IsCapacitatedMatching b x := by
  rw [isCapacitatedMatching_def, isCapacitatedMatching_def, ← f.vertexEquiv.forall_congr_right]
  refine forall_congr' fun v ↦ ?_
  have hv : ({f.vertexEquiv v} : Finset V(H)) =
      ({v} : Finset V(G)).map f.vertexEquiv.toEmbedding := by
    simp
  rw [hv, f.incidentEdges_map, Finset.sum_map]
  simp

/-- Isomorphic multigraphs are regular of the same degree. -/
theorem isRegularOfDegree_iff (f : Iso G H) (k : ℕ) :
    H.IsRegularOfDegree k ↔ G.IsRegularOfDegree k := by
  rw [isRegularOfDegree_def, isRegularOfDegree_def]
  refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [← f.encard_incidenceSet_vertexEquiv ⟨x, hx⟩]
    exact h _ (f.vertexEquiv _).2
  · simpa using (f.encard_incidenceSet_vertexEquiv (f.vertexEquiv.symm ⟨y, hy⟩)).trans
      (h _ (Subtype.prop _))

end Iso

end Graph
