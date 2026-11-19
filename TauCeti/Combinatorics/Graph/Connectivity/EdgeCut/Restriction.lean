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
subgraph, the cut along `T` consists exactly of the original cut edges whose two ends remain.  If
`T ⊆ S`, this is the original cut along `T` with the cut along `S` removed.  Vertex deletion is
the specialization to the vertices outside the deleted set.

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
theorem edgeCut_induce_eq_inter_edgeSet (G : Graph α β) (S T : Set α) :
    (G.induce S).edgeCut T = E(G.induce S) ∩ G.edgeCut T := by
  ext e
  rw [mem_edgeCut_iff, mem_inter_iff, mem_edgeCut_iff, edgeSet_induce]
  constructor
  · rintro ⟨x, y, ⟨hxy, hxS, hyS⟩, hxT, hyT⟩
    exact ⟨⟨x, y, hxy, hxS, hyS⟩, ⟨x, y, hxy, hxT, hyT⟩⟩
  · rintro ⟨heS, ⟨x, y, hxy, hxT, hyT⟩⟩
    obtain ⟨a, b, hab, haS, hbS⟩ := heS
    rcases hxy.eq_and_eq_or_eq_and_eq hab with h | h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, y, ⟨hxy, haS, hbS⟩, hxT, hyT⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, y, ⟨hxy, hbS, haS⟩, hxT, hyT⟩

/-- If `T ⊆ S`, restricting to `S` removes exactly the edges that cross the boundary of `S`
from the cut along `T`. -/
theorem edgeCut_induce_eq_sdiff (G : Graph α β) (hTS : T ⊆ S) :
    (G.induce S).edgeCut T = G.edgeCut T \ G.edgeCut S := by
  ext e
  rw [mem_edgeCut_iff, mem_sdiff, mem_edgeCut_iff]
  constructor
  · rintro ⟨x, y, ⟨hxy, hxS, hyS⟩, hxT, hyT⟩
    refine ⟨⟨x, y, hxy, hxT, hyT⟩, ?_⟩
    rw [hxy.mem_edgeCut_iff]
    tauto
  · rintro ⟨heT, heS⟩
    obtain ⟨x, y, hxy, hxT, hyT⟩ := heT
    have hxS := hTS hxT
    have hyS : y ∈ S := by
      by_contra hyS
      exact heS (mem_edgeCut_iff.mpr ⟨x, y, hxy, hxS, hyS⟩)
    exact ⟨x, y, ⟨hxy, hxS, hyS⟩, hxT, hyT⟩

/-- If every edge crossing `T` also crosses `S`, then no edge with both ends in `S` crosses `T`:
the subgraph induced on `S` has empty edge cut along `T`. -/
theorem edgeCut_induce_eq_empty_of_edgeCut_subset
    (h : G.edgeCut T ⊆ G.edgeCut S) : (G.induce S).edgeCut T = ∅ := by
  refine eq_empty_of_forall_notMem fun e he ↦ ?_
  obtain ⟨x, y, ⟨hxy, hxS, hyS⟩, hxT, hyT⟩ := mem_edgeCut_iff.mp he
  have := hxy.mem_edgeCut_iff.mp (h (mem_edgeCut_iff.mpr ⟨x, y, hxy, hxT, hyT⟩))
  tauto

/-- If `T ⊆ S` has empty edge cut in the subgraph induced on `S`, then every edge crossing `T`
also crosses `S`. -/
theorem edgeCut_subset_edgeCut_of_edgeCut_induce_eq_empty (hTS : T ⊆ S)
    (h : (G.induce S).edgeCut T = ∅) : G.edgeCut T ⊆ G.edgeCut S := by
  rw [edgeCut_induce_eq_sdiff G hTS, sdiff_eq_empty] at h
  exact h

/-- Deleting vertices retains exactly the original cut edges whose two ends survive. -/
theorem edgeCut_deleteVerts_eq_inter_edgeSet (G : Graph α β) (X T : Set α) :
    (G.deleteVerts X).edgeCut T = E(G.deleteVerts X) ∩ G.edgeCut T := by
  ext e
  rw [mem_edgeCut_iff, mem_inter_iff, mem_edgeCut_iff, edgeSet_deleteVerts]
  constructor
  · rintro ⟨x, y, hxy, hxT, hyT⟩
    rw [deleteVerts_isLink] at hxy
    exact ⟨⟨x, y, hxy⟩, ⟨x, y, hxy.1, hxT, hyT⟩⟩
  · rintro ⟨⟨a, b, hab, haX, hbX⟩, ⟨x, y, hxy, hxT, hyT⟩⟩
    rcases hxy.eq_and_eq_or_eq_and_eq hab with h | h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, y, (deleteVerts_isLink G X).2 ⟨hxy, haX, hbX⟩, hxT, hyT⟩
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨x, y, (deleteVerts_isLink G X).2 ⟨hxy, hbX, haX⟩, hxT, hyT⟩

/-- If `T` is disjoint from `X`, deleting `X` removes exactly the edges that cross the boundary of
`X` from the cut along `T`. -/
theorem edgeCut_deleteVerts_eq_sdiff (G : Graph α β) (hTX : Disjoint T X) :
    (G.deleteVerts X).edgeCut T = G.edgeCut T \ G.edgeCut X := by
  ext e
  rw [mem_edgeCut_iff, mem_sdiff, mem_edgeCut_iff]
  constructor
  · rintro ⟨x, y, hxy, hxT, hyT⟩
    rw [deleteVerts_isLink] at hxy
    refine ⟨⟨x, y, hxy.1, hxT, hyT⟩, ?_⟩
    rw [hxy.1.mem_edgeCut_iff]
    tauto
  · rintro ⟨heT, heX⟩
    obtain ⟨x, y, hxy, hxT, hyT⟩ := heT
    have hxX := Set.disjoint_left.1 hTX hxT
    have hyX : y ∉ X := by
      intro hyX
      exact heX (mem_edgeCut_iff.mpr ⟨y, x, hxy.symm, hyX, hxX⟩)
    exact ⟨x, y, (deleteVerts_isLink G X).2 ⟨hxy, hxX, hyX⟩, hxT, hyT⟩

end Graph
