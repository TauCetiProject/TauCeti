/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeCut

/-!
# Bonds of multigraphs

Mathlib defines a bond of a multigraph `G : Graph α β` as an inclusion-minimal nonempty edge
cut, `Graph.IsBond`.  This file characterizes bonds through the connectivity of the two sides of
the cut and relates bonds to closed subgraphs.

* `Graph.Connected.isBond_edgeCut_iff`: for a connected graph `G` and a set `S` of actual
  vertices, the edge cut of `S` is a bond exactly when both `S` and its complement `V(G) \ S`
  induce connected subgraphs.  Neither side need be assumed nonempty: the empty graph is not
  connected, and the edge cut of `∅` or of `V(G)` is empty.
* `Graph.IsBond.subset_edgeSet_of_isClosedSubgraph`: a bond meeting a closed subgraph, such as a
  connected component, lies inside it, and `Graph.IsClosedSubgraph.isBond_iff` shows that it is
  then a bond of that subgraph.
* `Graph.isBond_banana`: the edges joining two distinct vertices form a bond, so a bond may
  contain several parallel edges; with a single edge this is the bridge
  `Graph.isBridge_banana_singleton`, a singleton bond by `Graph.isBond_singleton_iff_isBridge`.

Minimality is by inclusion, independently of cardinality or capacity, and no finiteness is
assumed.  The characterization is the standard one; see R. Diestel, *Graph Theory*, 5th ed.,
Graduate Texts in Mathematics 173, Springer, 2017, Section 1.9.
-/

public section

open Set symmDiff

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β} {S : Set α} {B : Set β} {e : β} {x y : α}

/-- In a connected graph, if the edge cut of a set `S` of actual vertices is a bond, then `S`
induces a connected subgraph. -/
private theorem Connected.connected_induce_of_isBond (hG : G.Connected) (hS : S ⊆ V(G))
    (hB : G.IsBond (G.edgeCut S)) : (G.induce S).Connected := by
  -- Otherwise `S` splits into a reachability class `T` of the induced subgraph and its remainder
  -- `S \ T`.  Both have nonempty edge cuts contained in that of `S`, so by minimality both equal
  -- it, and their symmetric difference, the edge cut of `S`, is empty.
  obtain ⟨u, w, huw, hu, hw⟩ := mem_edgeCut_iff.mp hB.nonempty.some_mem
  refine connected_iff_forall_reachable.mpr ⟨⟨u, hu⟩, fun x y hx hy ↦ ?_⟩
  by_contra hxy
  set T := {z | (G.induce S).Reachable x z}
  have hTS : T ⊆ S := fun _ hz ↦ hz.right_mem
  have hT : (G.induce S).edgeCut T = ∅ := edgeCut_setOf_reachable _ x
  have hST : (G.induce S).edgeCut (S \ T) = ∅ := by
    have h := edgeCut_vertexSet_diff (G := G.induce S) (S := T)
    rwa [vertexSet_induce, hT] at h
  have hwV := huw.right_mem
  have h₁ := hB.eq_of_subset ⟨isEdgeCut_edgeCut _ _,
    (hG.reachable (hS hx) hwV).edgeCut_nonempty (Reachable.refl hx) fun h ↦ hw (hTS h)⟩
    (edgeCut_subset_edgeCut_of_edgeCut_induce_eq_empty hTS hT)
  have h₂ := hB.eq_of_subset ⟨isEdgeCut_edgeCut _ _,
    (hG.reachable (hS hy) hwV).edgeCut_nonempty (S := S \ T) ⟨hy, hxy⟩ fun h ↦ hw h.1⟩
    (edgeCut_subset_edgeCut_of_edgeCut_induce_eq_empty sdiff_subset hST)
  have hsymm : T ∆ (S \ T) = S := by
    rw [disjoint_sdiff_right.symmDiff_eq_sup]
    exact union_sdiff_cancel hTS
  have hempty := G.edgeCut_symmDiff (S := T) (S' := S \ T)
  rw [hsymm, h₁, h₂, symmDiff_self] at hempty
  exact hB.nonempty.ne_empty hempty

/-- **Bonds by connected sides.**  In a connected graph `G`, the edge cut of a set `S` of actual
vertices is a bond exactly when both `S` and `V(G) \ S` induce connected subgraphs. -/
theorem Connected.isBond_edgeCut_iff (hG : G.Connected) (hS : S ⊆ V(G)) :
    G.IsBond (G.edgeCut S) ↔ (G.induce S).Connected ∧ (G.induce (V(G) \ S)).Connected := by
  refine ⟨fun hB ↦ ⟨hG.connected_induce_of_isBond hS hB,
    hG.connected_induce_of_isBond sdiff_subset (by rwa [edgeCut_vertexSet_diff])⟩,
    fun ⟨hSc, hCc⟩ ↦ ?_⟩
  obtain ⟨u, hu⟩ := hSc.nonempty
  obtain ⟨w, hwV, hwS⟩ := hCc.nonempty
  refine ⟨⟨isEdgeCut_edgeCut G S, (hG.reachable (hS hu) hwV).edgeCut_nonempty hu hwS⟩,
    fun F ⟨hF, f, hf⟩ hFS ↦ ?_⟩
  obtain ⟨T, -, rfl⟩ := hF.exists_edgeCut
  -- Membership in `T` is constant on each side of the cut, since each side is connected and
  -- none of its edges crosses `T`.
  have hconst {R : Set α} (hR : (G.induce R).Connected) (hTR : G.edgeCut T ⊆ G.edgeCut R)
      {a b : α} (ha : a ∈ R) (hb : b ∈ R) : a ∈ T ↔ b ∈ T :=
    have hRT := edgeCut_induce_eq_empty_of_edgeCut_subset hTR
    ⟨(hR.reachable ha hb).mem_of_edgeCut_eq_empty hRT,
      (hR.reachable hb ha).mem_of_edgeCut_eq_empty hRT⟩
  have hTC : G.edgeCut T ⊆ G.edgeCut (V(G) \ S) := by rwa [edgeCut_vertexSet_diff]
  obtain ⟨a, b, hab, haT, hbT⟩ := mem_edgeCut_iff.mp hf
  have haV := hab.left_mem
  have hbV := hab.right_mem
  intro e he
  obtain ⟨p, q, hpq, hpS, hqS⟩ := mem_edgeCut_iff.mp he
  have hqV := hpq.right_mem
  rw [hpq.mem_edgeCut_iff]
  rcases hab.mem_edgeCut_iff.mp (hFS hf) with ⟨haS, hbS⟩ | ⟨hbS, haS⟩
  · exact .inl ⟨(hconst hSc hFS hpS haS).mpr haT,
      fun hq ↦ hbT ((hconst hCc hTC ⟨hqV, hqS⟩ ⟨hbV, hbS⟩).mp hq)⟩
  · exact .inr ⟨(hconst hCc hTC ⟨hqV, hqS⟩ ⟨haV, haS⟩).mpr haT,
      fun hp ↦ hbT ((hconst hSc hFS hpS hbS).mp hp)⟩

/-! ### Bonds and closed subgraphs -/

/-- A bond sharing an edge with a closed subgraph, such as a connected component, lies inside
that subgraph. -/
theorem IsBond.subset_edgeSet_of_isClosedSubgraph (hB : G.IsBond B) (hHG : H ≤c G)
    (heB : e ∈ B) (heH : e ∈ E(H)) : B ⊆ E(H) := by
  have h := hB.eq_of_subset ⟨(hB.isEdgeCut.inter_edgeSet_of_le hHG.le).of_isClosedSubgraph hHG,
    e, heH, heB⟩ inter_subset_right
  exact h ▸ inter_subset_left

/-- A bond of `G` whose edges lie in a closed subgraph `H` is a bond of `H`. -/
theorem IsBond.anti_of_isClosedSubgraph (hHG : H ≤c G) (hBH : B ⊆ E(H)) (hB : G.IsBond B) :
    H.IsBond B :=
  ⟨⟨hB.isEdgeCut.anti_of_subset hHG.le hBH, hB.nonempty⟩,
    fun _ ⟨hF, hFne⟩ hFB ↦ hB.2 ⟨hF.of_isClosedSubgraph hHG, hFne⟩ hFB⟩

/-- For a set of edges of a closed subgraph `H` of `G`, such as a connected component, being a
bond of `H` and being a bond of `G` agree. -/
theorem IsClosedSubgraph.isBond_iff (hBH : B ⊆ E(H)) (hHG : H ≤c G) :
    G.IsBond B ↔ H.IsBond B :=
  ⟨IsBond.anti_of_isClosedSubgraph hHG hBH, IsBond.of_isClosedSubgraph hHG⟩

/-! ### Graphs on two vertices -/

/-- The nonempty set of edges joining two distinct vertices is a bond of the graph they form:
both sides of the cut are single vertices. -/
theorem isBond_banana {u w : α} (huw : u ≠ w) {F : Set β} (hF : F.Nonempty) :
    (banana u w F).IsBond F := by
  have hG : (banana u w F).Connected := componentCount_eq_one_iff.mp (componentCount_banana hF)
  have h := hG.isBond_edgeCut_iff (S := {u}) (by simp)
  rw [edgeCut_banana_singleton huw F] at h
  refine h.mpr ⟨connected_of_vertexSet_eq_singleton (vertexSet_induce _ _),
    connected_of_vertexSet_eq_singleton (x := w) ?_⟩
  rw [vertexSet_induce, vertexSet_banana, insert_sdiff_self_of_notMem (by simpa using huw)]

end Graph
