/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic

import all Mathlib.Combinatorics.Graph.Connected.EdgeCut

/-!
# Walks and edge cuts

This file relates Mathlib's edge cuts `Graph.edgeCut` to edge-labelled multigraph walks.
A walk that starts inside a vertex set and ends outside it traverses an edge of the cut, so a
vertex set is closed under reachability exactly when its edge cut is empty.  In particular, the
set of vertices reachable from a point has empty edge cut.  Deleting edges removes them from every
edge cut, and loops never cross a cut.

If the edge cut of `T` is contained in that of `S`, then the subgraph induced on `S` has empty
edge cut along `T`; conversely when `T ⊆ S`.

These facts are the interface between cut-based and walk-based descriptions of connectivity,
used for instance to characterize bridges by deletion.

## Implementation notes

Mathlib does not expose the body of `Graph.IsEdgeCut` and provides only elimination lemmas for it,
so no edge cut can be produced outside its defining module. `Graph.isEdgeCut_iff` supplies the
missing characterization; its proof unfolds the definition through `import all`.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {S : Set α} {e : β} {x y : α}

/-- A set of edges is an edge cut exactly when it is the edge cut of some vertex set. -/
theorem isEdgeCut_iff {F : Set β} : G.IsEdgeCut F ↔ ∃ S : Set α, G.edgeCut S = F := Iff.rfl

/-- The edge cut of a vertex set is an edge cut. -/
@[simp]
theorem isEdgeCut_edgeCut (G : Graph α β) (S : Set α) : G.IsEdgeCut (G.edgeCut S) :=
  isEdgeCut_iff.mpr ⟨S, rfl⟩

/-- Deleting a set of edges removes exactly those edges from every edge cut. -/
@[simp]
theorem edgeCut_deleteEdges (G : Graph α β) (F : Set β) (S : Set α) :
    (G.deleteEdges F).edgeCut S = G.edgeCut S \ F := by
  ext e
  simp only [mem_edgeCut_iff, deleteEdges_isLink, mem_sdiff]
  grind

/-- A loop never crosses an edge cut. -/
theorem IsLoopAt.notMem_edgeCut (h : G.IsLoopAt e x) : e ∉ G.edgeCut S := by
  rw [IsLink.mem_edgeCut_iff h]
  tauto

/-- A walk from a vertex inside `S` to a point outside `S` traverses an edge of the edge cut
of `S`. -/
theorem Walk.exists_mem_edges_mem_edgeCut (p : G.Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ e ∈ p.edges, e ∈ G.edgeCut S := by
  induction p with
  | nil => exact absurd hx hy
  | @cons x z y f hf p ih =>
    by_cases hz : z ∈ S
    · obtain ⟨e, he, heS⟩ := ih hz hy
      exact ⟨e, by simp [he], heS⟩
    · exact ⟨f, by simp, mem_edgeCut_iff.mpr ⟨x, z, hf, hx, hz⟩⟩

/-- A vertex set has empty edge cut exactly when it is closed under reachability. -/
theorem edgeCut_eq_empty_iff_forall_reachable :
    G.edgeCut S = ∅ ↔ ∀ ⦃x y⦄, G.Reachable x y → x ∈ S → y ∈ S := by
  constructor
  · intro hS x y h hx
    by_contra hy
    obtain ⟨p⟩ := (reachable_def.mp h).2
    obtain ⟨e, -, he⟩ := p.exists_mem_edges_mem_edgeCut hx hy
    simp [hS] at he
  · intro hS
    ext e
    simp only [mem_edgeCut_iff, mem_empty_iff_false, iff_false, not_exists, not_and]
    exact fun x y h hx hy ↦ hy (hS h.reachable hx)

/-- Reachability does not leave a vertex set with empty edge cut. -/
theorem Reachable.mem_of_edgeCut_eq_empty (h : G.Reachable x y) (hS : G.edgeCut S = ∅)
    (hx : x ∈ S) : y ∈ S :=
  edgeCut_eq_empty_iff_forall_reachable.mp hS h hx

/-- The set of points reachable from a fixed point has empty edge cut. -/
@[simp]
theorem edgeCut_setOf_reachable (G : Graph α β) (x : α) :
    G.edgeCut {y | G.Reachable x y} = ∅ :=
  edgeCut_eq_empty_iff_forall_reachable.mpr fun _ _ h hx ↦ Reachable.trans hx h

/-! ### Edge cuts of induced subgraphs -/

/-- If every edge crossing `T` also crosses `S`, then no edge with both ends in `S` crosses `T`:
the subgraph induced on `S` has empty edge cut along `T`. -/
theorem edgeCut_induce_eq_empty_of_edgeCut_subset {T : Set α}
    (h : G.edgeCut T ⊆ G.edgeCut S) : (G.induce S).edgeCut T = ∅ := by
  refine eq_empty_of_forall_notMem fun e he ↦ ?_
  obtain ⟨x, y, ⟨hxy, hxS, hyS⟩, hxT, hyT⟩ := mem_edgeCut_iff.mp he
  have := hxy.mem_edgeCut_iff.mp (h (mem_edgeCut_iff.mpr ⟨x, y, hxy, hxT, hyT⟩))
  tauto

/-- If `T ⊆ S` has empty edge cut in the subgraph induced on `S`, then every edge crossing `T`
also crosses `S`. -/
theorem edgeCut_subset_edgeCut_of_edgeCut_induce_eq_empty {T : Set α} (hTS : T ⊆ S)
    (h : (G.induce S).edgeCut T = ∅) : G.edgeCut T ⊆ G.edgeCut S := by
  rintro e ⟨x, y, hxy, hxT, hyT⟩
  refine mem_edgeCut_iff.mpr ⟨x, y, hxy, hTS hxT, fun hyS ↦ ?_⟩
  have he : e ∈ (G.induce S).edgeCut T :=
    mem_edgeCut_iff.mpr ⟨x, y, ⟨hxy, hTS hxT, hyS⟩, hxT, hyT⟩
  rw [h] at he
  exact he

end Graph
