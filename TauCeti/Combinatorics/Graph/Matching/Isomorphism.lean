/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Isomorphism
public import TauCeti.Combinatorics.Graph.Matching.Capacitated

/-!
# Isomorphism invariance of matchings

A multigraph isomorphism transports sets of actual edges by its edge equivalence. This transport
preserves and reflects matchings and perfect matchings. Pulling vertex capacities and edge
multiplicities back along the isomorphism preserves and reflects multiset capacitated matchings.
Edge identities are part of the isomorphism, so parallel edges and loops are treated exactly as in
the original graph.

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

end Iso

end Graph
