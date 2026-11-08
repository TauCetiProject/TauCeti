/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Delete
public import TauCeti.Combinatorics.Graph.Incidence

/-!
# Matchings and perfect matchings of multigraphs

Let `G : Graph α β` be a multigraph, possibly with loops and parallel edges. A *matching* of `G`
is a set `M` of actual edge identities, none of them a loop, such that no two distinct edges of
`M` have a common end. It is *perfect* when moreover every actual vertex is an end of an edge of
`M`, which is then unique. Two parallel edges are distinct edge identities, so a matching contains
at most one of them.

Matchings are sets of edge identities rather than subgraphs, so that removing a perfect matching
is edge deletion. Removing a perfect matching lowers the incidence count of every actual vertex by
exactly one; this is the step that splits the edge set of a regular bipartite multigraph into
perfect matchings.

## Main definitions

* `Graph.IsMatching G M`: the set `M` of edges is a matching of `G`.
* `Graph.IsPerfectMatching G M`: the set `M` of edges is a perfect matching of `G`.

## Main results

* `Graph.IsSubgraph.isMatching_iff`: a set of edges of a subgraph `H ≤ G` is a matching of `H`
  exactly when it is a matching of `G`.
* `Graph.IsSpanningSubgraph.isPerfectMatching_iff`: the same for perfect matchings and spanning
  subgraphs.
* `Graph.IsPerfectMatching.existsUnique_inc`: every actual vertex is an end of exactly one edge of
  a perfect matching.
* `Graph.IsPerfectMatching.incidenceCount_deleteEdges_add_one`: deleting a perfect matching lowers
  every incidence count by one.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β} {M N : Set β} {x : α}

variable (G) in
/-- The set `M` of edge identities is a *matching* of the multigraph `G`: its members are actual
edges of `G`, none of them is a loop, and two of them with a common end are equal. -/
structure IsMatching (M : Set β) : Prop where
  subset_edgeSet : M ⊆ E(G)
  not_isLoopAt ⦃e : β⦄ (he : e ∈ M) (x : α) : ¬ G.IsLoopAt e x
  eq_of_inc ⦃e f : β⦄ ⦃x : α⦄ (he : e ∈ M) (hf : f ∈ M) (hex : G.Inc e x) (hfx : G.Inc f x) :
    e = f

variable (G) in
/-- The set `M` of edge identities is a *perfect matching* of the multigraph `G`: it is a matching
of `G`, and every actual vertex of `G` is an end of an edge of `M`. -/
structure IsPerfectMatching (M : Set β) : Prop extends G.IsMatching M where
  exists_inc ⦃x : α⦄ (hx : x ∈ V(G)) : ∃ e ∈ M, G.Inc e x

/-- The empty set of edges is a matching. -/
@[simp]
theorem isMatching_empty : G.IsMatching ∅ where
  subset_edgeSet := empty_subset _
  not_isLoopAt _ he := he.elim
  eq_of_inc _ _ _ he := he.elim

namespace IsMatching

/-- A subset of a matching is a matching. -/
theorem subset (h : G.IsMatching M) (hNM : N ⊆ M) : G.IsMatching N where
  subset_edgeSet := hNM.trans h.subset_edgeSet
  not_isLoopAt _ he := h.not_isLoopAt (hNM he)
  eq_of_inc _ _ _ he hf := h.eq_of_inc (hNM he) (hNM hf)

/-- An actual vertex is an end of at most one edge of a matching. -/
theorem subsingleton_incidenceSet_inter (h : G.IsMatching M) (x : α) :
    (G.incidenceSet x ∩ M).Subsingleton :=
  fun _ he _ hf ↦ h.eq_of_inc he.2 hf.2 he.1 hf.1

end IsMatching

/-- A set of edges of a subgraph `H` of `G` is a matching of `H` exactly when it is a matching of
`G`. -/
theorem IsSubgraph.isMatching_iff (hHG : H ≤ G) (hM : M ⊆ E(H)) :
    H.IsMatching M ↔ G.IsMatching M := by
  have hinc {e} (he : e ∈ M) {x} : H.Inc e x ↔ G.Inc e x := hHG.inc_congr (hM he)
  have hloop {e} (he : e ∈ M) {x} : H.IsLoopAt e x ↔ G.IsLoopAt e x :=
    hHG.isLoopAt_congr (hM he)
  refine ⟨fun h ↦ ⟨hM.trans hHG.edgeSet_mono, fun e he x ↦ ?_, fun e f x he hf hex hfx ↦ ?_⟩,
    fun h ↦ ⟨hM, fun e he x ↦ ?_, fun e f x he hf hex hfx ↦ ?_⟩⟩
  · exact (hloop he).not.1 (h.not_isLoopAt he x)
  · exact h.eq_of_inc he hf ((hinc he).2 hex) ((hinc hf).2 hfx)
  · exact (hloop he).not.2 (h.not_isLoopAt he x)
  · exact h.eq_of_inc he hf ((hinc he).1 hex) ((hinc hf).1 hfx)

/-- A set of edges of a spanning subgraph `H` of `G` is a perfect matching of `H` exactly when it
is a perfect matching of `G`. -/
theorem IsSpanningSubgraph.isPerfectMatching_iff (hHG : H ≤s G) (hM : M ⊆ E(H)) :
    H.IsPerfectMatching M ↔ G.IsPerfectMatching M := by
  have hinc {e} (he : e ∈ M) {x} : H.Inc e x ↔ G.Inc e x := hHG.le.inc_congr (hM he)
  refine ⟨fun h ↦ ⟨(hHG.le.isMatching_iff hM).1 h.toIsMatching, fun x hx ↦ ?_⟩,
    fun h ↦ ⟨(hHG.le.isMatching_iff hM).2 h.toIsMatching, fun x hx ↦ ?_⟩⟩
  · obtain ⟨e, he, hex⟩ := h.exists_inc (hHG.vertexSet_eq ▸ hx)
    exact ⟨e, he, (hinc he).1 hex⟩
  · obtain ⟨e, he, hex⟩ := h.exists_inc (hHG.vertexSet_eq ▸ hx)
    exact ⟨e, he, (hinc he).2 hex⟩

namespace IsPerfectMatching

/-- Every actual vertex is an end of exactly one edge of a perfect matching. -/
theorem existsUnique_inc (h : G.IsPerfectMatching M) (hx : x ∈ V(G)) :
    ∃! e, e ∈ M ∧ G.Inc e x := by
  obtain ⟨e, he, hex⟩ := h.exists_inc hx
  exact ⟨e, ⟨he, hex⟩, fun f hf ↦ h.eq_of_inc hf.1 he hf.2 hex⟩

/-- Exactly one edge of a perfect matching is incident with each actual vertex. -/
theorem ncard_incidenceSet_inter (h : G.IsPerfectMatching M) (hx : x ∈ V(G)) :
    (G.incidenceSet x ∩ M).ncard = 1 := by
  obtain ⟨e, he, hex⟩ := h.exists_inc hx
  exact ncard_eq_one.2 ⟨e, eq_singleton_iff_unique_mem.2
    ⟨⟨hex, he⟩, fun f hf ↦ h.eq_of_inc hf.2 he hf.1 hex⟩⟩

/-- Deleting a perfect matching lowers the incidence count of every actual vertex with finitely
many incident edges by exactly one. -/
theorem incidenceCount_deleteEdges_add_one (h : G.IsPerfectMatching M) (hx : x ∈ V(G))
    (hfin : (G.incidenceSet x).Finite) :
    (G.deleteEdges M).incidenceCount x + 1 = G.incidenceCount x := by
  rw [← h.ncard_incidenceSet_inter hx, G.incidenceCount_deleteEdges_add_ncard_inter M x hfin]

end IsPerfectMatching

end Graph
