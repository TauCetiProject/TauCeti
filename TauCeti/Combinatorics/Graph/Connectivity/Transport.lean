/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.VertexConnectivity
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Isomorphism
public import TauCeti.Combinatorics.Graph.Simple

/-!
# Isomorphism invariance of multigraph connectivity

Multigraph isomorphisms preserve local and global edge- and vertex-connectivity, and their
numerical invariants. The edge statements retain edge identities: a deleted edge set is
transported by the edge equivalence, so loops and parallel edges need no special treatment.
The vertex statements use the induced isomorphism of underlying simple graphs.

All endpoints are actual vertices. No finiteness is needed, either for the graph carriers or
for their ambient types; in particular the results include infinite connectivity and the
empty-graph conventions.
-/

public section

open Set

universe u v u' v'

namespace Graph.Iso

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G : Graph α β} {H : Graph α' β'}

/-- An isomorphism transports reachability after deleting an edge set. Edges outside the
actual edge set are discarded by `mapEdgeSet` and have no effect on reachability. -/
theorem reachable_deleteEdges_mapEdgeSet_iff (f : Iso G H) (F : Set β) (x y : V(G)) :
    (H.deleteEdges (f.mapEdgeSet F)).Reachable (f.vertexEquiv x) (f.vertexEquiv y) ↔
      (G.deleteEdges F).Reachable x y := by
  simp only [reachable_deleteEdges_iff_exists_walk, Subtype.prop, true_and]
  constructor
  · rintro ⟨p, hp⟩
    have havoid : ∀ e ∈ (f.symm.mapWalk p).edges, e ∉ F := by
      intro e he heF
      let e' : G.edgeSet := ⟨e, (f.symm.mapWalk p).edges_subset_edgeSet he⟩
      have hem : (f.edgeEquiv e' : β') ∈ p.edges :=
        (f.symm.edgeEquiv_mem_edges_mapWalk_iff p (f.edgeEquiv e')).mp
          (by simpa [e'] using he)
      exact hp _ hem (by simpa using heF)
    exact ⟨(f.symm.mapWalk p).copy
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv x))
      (congrArg Subtype.val (f.symm_vertexEquiv_apply_vertexEquiv y)), by
        simpa using havoid⟩
  · rintro ⟨p, hp⟩
    refine ⟨f.mapWalk p, fun e he heF ↦ ?_⟩
    let e' : H.edgeSet := ⟨e, (f.mapWalk p).edges_subset_edgeSet he⟩
    have hem : (f.edgeEquiv.symm e' : β) ∈ p.edges :=
      (f.edgeEquiv_mem_edges_mapWalk_iff p (f.edgeEquiv.symm e')).mp
        (by simpa [e'] using he)
    exact hp _ hem ((f.mem_mapEdgeSet_iff F e').mp heF)

/-- Edge reachability at every natural threshold is invariant under multigraph isomorphism. -/
@[simp]
theorem isEdgeReachable_iff (f : Iso G H) (k : ℕ) (x y : V(G)) :
    H.IsEdgeReachable k (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.IsEdgeReachable k x y := by
  rw [isEdgeReachable_iff_forall_subset_edgeSet, isEdgeReachable_iff_forall_subset_edgeSet]
  constructor
  · intro h F hF hcard
    exact (f.reachable_deleteEdges_mapEdgeSet_iff F x y).mp
      (h (f.mapEdgeSet_subset_edgeSet F) (by simpa only [f.encard_mapEdgeSet hF] using hcard))
  · intro h F hF hcard
    have hr := h (f.symm.mapEdgeSet_subset_edgeSet F)
      (by simpa only [f.symm.encard_mapEdgeSet hF] using hcard)
    have ht := (f.reachable_deleteEdges_mapEdgeSet_iff (f.symm.mapEdgeSet F) x y).mpr hr
    have hround := f.symm.symm_mapEdgeSet_mapEdgeSet hF
    rw [symm_symm] at hround
    rwa [hround] at ht

/-- Global edge connectivity is invariant under multigraph isomorphism, including for empty
actual vertex sets. -/
theorem isEdgeConnected_iff (f : Iso G H) (k : ℕ) :
    H.IsEdgeConnected k ↔ G.IsEdgeConnected k := by
  simp only [isEdgeConnected_def]
  constructor
  · intro h x hx y hy
    exact (f.isEdgeReachable_iff k ⟨x, hx⟩ ⟨y, hy⟩).mp
      (h (f.vertexEquiv ⟨x, hx⟩).2 (f.vertexEquiv ⟨y, hy⟩).2)
  · intro h x hx y hy
    have hr := (f.isEdgeReachable_iff k (f.vertexEquiv.symm ⟨x, hx⟩)
      (f.vertexEquiv.symm ⟨y, hy⟩)).mpr
        (h (f.vertexEquiv.symm ⟨x, hx⟩).2 (f.vertexEquiv.symm ⟨y, hy⟩).2)
    simpa using hr

/-- Local numerical edge reachability is unchanged by a multigraph isomorphism. -/
@[simp]
theorem edgeReachability_eq (f : Iso G H) (x y : V(G)) :
    H.edgeReachability (f.vertexEquiv x) (f.vertexEquiv y) = G.edgeReachability x y := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  simp only [← isEdgeReachable_iff_le_edgeReachability, f.isEdgeReachable_iff]

/-- Numerical edge connectivity is unchanged by a multigraph isomorphism. -/
theorem edgeConnectivity_eq (f : Iso G H) : H.edgeConnectivity = G.edgeConnectivity := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  simp only [← isEdgeConnected_iff_le_edgeConnectivity, f.isEdgeConnected_iff]

/-- Local vertex reachability is invariant under multigraph isomorphism. -/
@[simp]
theorem isVertexReachable_iff (f : Iso G H) (k : ℕ) (x y : V(G)) :
    H.IsVertexReachable k (f.vertexEquiv x) (f.vertexEquiv y) ↔ G.IsVertexReachable k x y := by
  simpa only [toSimpleGraphIso_apply] using
    (f.toSimpleGraphIso.isVertexReachable_iff (k := (k : ℕ∞)) x y)

/-- Global vertex connectivity is invariant under multigraph isomorphism. -/
theorem isVertexConnected_iff (f : Iso G H) (k : ℕ) :
    H.IsVertexConnected k ↔ G.IsVertexConnected k :=
  f.toSimpleGraphIso.isVertexConnected_iff

/-- Numerical vertex connectivity is unchanged by a multigraph isomorphism, including on the
empty actual vertex set. -/
theorem vertexConnectivity_eq (f : Iso G H) : H.vertexConnectivity = G.vertexConnectivity :=
  f.toSimpleGraphIso.vertexConnectivity_eq

end Graph.Iso
