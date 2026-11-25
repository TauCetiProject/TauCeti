/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.EdgeCut.Basic

/-!
# Edge cuts under vertex restriction

This file computes edge cuts after restricting a multigraph to a set of vertices.  In an induced
subgraph, the cut along `T` consists exactly of the original cut edges whose two ends remain.  It
is the original cut along `T ∩ S` with the cut along `S` removed.  Vertex deletion is the
specialization to the vertices outside the deleted set.

The formulas do not require the restricting set to lie in the graph's vertex set.  This matters
because `Graph.induce S` is defined for every ambient set `S`; in that generality it need not be a
subgraph in Mathlib's sense, even though its edges are inherited from the original graph.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {S T X : Set α}

/-- Restricting to an induced subgraph retains exactly the original cut edges whose two ends lie
in the inducing set. -/
theorem edgeCut_induce_eq_inter (G : Graph α β) (S T : Set α) :
    (G.induce S).edgeCut T = E(G.induce S) ∩ G.edgeCut T := by
  ext e
  grind [edgeSet_eq_setOfPred_exists_isLink, IsLink.mem_edgeCut_iff]

/-- Restricting to `S` removes exactly the edges that cross the boundary of `S` from the cut along
the part of `T` that survives in `S`. -/
theorem edgeCut_induce_eq_sdiff (G : Graph α β) (S T : Set α) :
    (G.induce S).edgeCut T = G.edgeCut (T ∩ S) \ G.edgeCut S := by
  ext e
  grind [IsLink.mem_edgeCut_iff]

/-- If every edge crossing `T` also crosses `S`, then no edge with both ends in `S` crosses `T`:
the subgraph induced on `S` has empty edge cut along `T`. -/
theorem edgeCut_induce_eq_empty_of_edgeCut_subset
    (h : G.edgeCut T ⊆ G.edgeCut S) : (G.induce S).edgeCut T = ∅ := by
  refine eq_empty_of_forall_notMem fun e he ↦ ?_
  obtain ⟨x, y, hxy, hxT, hyT⟩ := mem_edgeCut_iff.mp he
  rw [induce_isLink] at hxy
  have := hxy.1.mem_edgeCut_iff.mp (h (mem_edgeCut_iff.mpr ⟨x, y, hxy.1, hxT, hyT⟩))
  tauto

/-- If `T ⊆ S` has empty edge cut in the subgraph induced on `S`, then every edge crossing `T`
also crosses `S`. -/
theorem edgeCut_subset_edgeCut_of_edgeCut_induce_eq_empty (hTS : T ⊆ S)
    (h : (G.induce S).edgeCut T = ∅) : G.edgeCut T ⊆ G.edgeCut S := by
  rw [edgeCut_induce_eq_sdiff, inter_eq_left.2 hTS, sdiff_eq_empty] at h
  exact h

/-- Deleting `X` removes exactly the edges that cross the boundary of `X` from the cut along the
part of `T` outside `X`. -/
theorem edgeCut_deleteVerts_eq_sdiff (G : Graph α β) (X T : Set α) :
    (G.deleteVerts X).edgeCut T = G.edgeCut (T \ X) \ G.edgeCut X := by
  ext e
  grind [IsLink.mem_edgeCut_iff]

end Graph
