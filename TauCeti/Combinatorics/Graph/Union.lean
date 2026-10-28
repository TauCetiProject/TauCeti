/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Unions of compatible multigraphs

This file constructs the union of two compatible `Graph`s. Its vertices and edges are the
set-theoretic unions, and an edge is linked exactly when it is linked in either input graph.
Compatibility is essential: a shared edge must not acquire two different pairs of endpoints.

The union is the least common supergraph of its inputs. Compatible unions commute, and unions of
three pairwise compatible graphs associate. These facts let graph constructions grow a subgraph
one compatible piece at a time while retaining the original vertex and edge types.

The interface is the compatible fragment of the union design in
[Mathlib pull request #38337](https://github.com/leanprover-community/mathlib4/pull/38337).
Unlike that proposal, no choice of incidence is made for incompatible shared edges.
-/

public section

open Set

variable {α β : Type*} {G H K : Graph α β} {e : β} {x y : α}

namespace Graph

namespace Compatible

/-- The union of compatible graphs. Its vertices, edges, and links are the corresponding unions. -/
protected def union (h : G.Compatible H) : Graph α β where
  vertexSet := V(G) ∪ V(H)
  edgeSet := E(G) ∪ E(H)
  IsLink e x y := G.IsLink e x y ∨ H.IsLink e x y
  isLink_symm _ _ := {
    symm := by
      rintro x y (hxy | hxy)
      · exact Or.inl hxy.symm
      · exact Or.inr hxy.symm }
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w (hxy | hxy) (hvw | hvw)
    · exact hxy.left_eq_or_eq hvw
    · exact ((h.isLink_congr hxy.edge_mem hvw.edge_mem).mp hxy).left_eq_or_eq hvw
    · exact hxy.left_eq_or_eq ((h.isLink_congr hvw.edge_mem hxy.edge_mem).mp hvw)
    · exact hxy.left_eq_or_eq hvw
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · rintro (he | he)
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
        exact ⟨x, y, Or.inl hxy⟩
      · obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
        exact ⟨x, y, Or.inr hxy⟩
    · rintro ⟨x, y, hxy | hxy⟩
      · exact Or.inl hxy.edge_mem
      · exact Or.inr hxy.edge_mem
  left_mem_of_isLink := by
    rintro e x y (hxy | hxy)
    · exact Or.inl hxy.left_mem
    · exact Or.inr hxy.left_mem

@[simp]
theorem vertexSet_union (h : G.Compatible H) : V(h.union) = V(G) ∪ V(H) :=
  Eq.refl _

@[simp]
theorem edgeSet_union (h : G.Compatible H) : E(h.union) = E(G) ∪ E(H) :=
  Eq.refl _

@[simp]
theorem union_isLink (h : G.Compatible H) :
    h.union.IsLink e x y ↔ G.IsLink e x y ∨ H.IsLink e x y :=
  (Iff.rfl)

@[simp]
theorem union_inc_iff (h : G.Compatible H) :
    h.union.Inc e x ↔ G.Inc e x ∨ H.Inc e x := by
  constructor
  · rintro ⟨y, hxy⟩
    exact h.union_isLink.mp hxy |>.imp (fun hxy ↦ ⟨y, hxy⟩) (fun hxy ↦ ⟨y, hxy⟩)
  · rintro (⟨y, hxy⟩ | ⟨y, hxy⟩)
    · exact ⟨y, h.union_isLink.mpr (Or.inl hxy)⟩
    · exact ⟨y, h.union_isLink.mpr (Or.inr hxy)⟩

@[simp]
theorem union_adj_iff (h : G.Compatible H) :
    h.union.Adj x y ↔ G.Adj x y ∨ H.Adj x y := by
  constructor
  · rintro ⟨e, hxy⟩
    exact h.union_isLink.mp hxy |>.imp (fun hxy ↦ ⟨e, hxy⟩) (fun hxy ↦ ⟨e, hxy⟩)
  · rintro (⟨e, hxy⟩ | ⟨e, hxy⟩)
    · exact ⟨e, h.union_isLink.mpr (Or.inl hxy)⟩
    · exact ⟨e, h.union_isLink.mpr (Or.inr hxy)⟩

@[simp]
theorem union_isLoopAt_iff (h : G.Compatible H) :
    h.union.IsLoopAt e x ↔ G.IsLoopAt e x ∨ H.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
theorem union_isNonloopAt_iff (h : G.Compatible H) :
    h.union.IsNonloopAt e x ↔ G.IsNonloopAt e x ∨ H.IsNonloopAt e x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact h.union_isLink.mp hxy |>.imp (fun hxy ↦ ⟨y, hy, hxy⟩) (fun hxy ↦ ⟨y, hy, hxy⟩)
  · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩)
    · exact ⟨y, hy, h.union_isLink.mpr (Or.inl hxy)⟩
    · exact ⟨y, hy, h.union_isLink.mpr (Or.inr hxy)⟩

/-- The left input is a subgraph of a compatible union. -/
@[simp]
theorem left_le_union (h : G.Compatible H) : G ≤ h.union where
  vertexSet_mono := subset_union_left
  isLink_mono := by
    intro e x y hxy
    exact h.union_isLink.mpr (Or.inl hxy)

/-- The right input is a subgraph of a compatible union. -/
@[simp]
theorem right_le_union (h : G.Compatible H) : H ≤ h.union where
  vertexSet_mono := subset_union_right
  isLink_mono := by
    intro e x y hxy
    exact h.union_isLink.mpr (Or.inr hxy)

/-- A compatible union is contained in a graph exactly when both inputs are contained in it. -/
@[simp]
theorem union_le_iff (h : G.Compatible H) : h.union ≤ K ↔ G ≤ K ∧ H ≤ K := by
  constructor
  · intro hle
    exact ⟨h.left_le_union.trans hle, h.right_le_union.trans hle⟩
  · rintro ⟨hG, hH⟩
    exact ⟨union_subset hG.vertexSet_mono hH.vertexSet_mono, by
      rintro e x y (hxy | hxy)
      · exact hG.isLink_mono hxy
      · exact hH.isLink_mono hxy⟩

/-- Compatible union is commutative. -/
theorem union_comm (h : G.Compatible H) : h.union = h.symm.union := by
  apply Graph.ext
  · exact Set.union_comm V(G) V(H)
  · intro e x y
    rw [h.union_isLink, h.symm.union_isLink, or_comm]

/-- The union of `G` and `H` is compatible with `K` when all three graphs are pairwise
compatible. -/
theorem union_compatible (hGH : G.Compatible H) (hGK : G.Compatible K)
    (hHK : H.Compatible K) : hGH.union.Compatible K := by
  intro e heGH heK x y
  constructor
  · rintro (hxy | hxy)
    · exact (hGK.isLink_congr hxy.edge_mem heK).mp hxy
    · exact (hHK.isLink_congr hxy.edge_mem heK).mp hxy
  · intro hxy
    rcases heGH with heG | heH
    · exact Or.inl ((hGK.isLink_congr heG heK).mpr hxy)
    · exact Or.inr ((hHK.isLink_congr heH heK).mpr hxy)

/-- `G` is compatible with the union of `H` and `K` when all three graphs are pairwise
compatible. -/
theorem compatible_union (hGH : G.Compatible H) (hGK : G.Compatible K)
    (hHK : H.Compatible K) : G.Compatible hHK.union :=
  (hHK.union_compatible hGH.symm hGK.symm).symm

/-- Compatible union is associative for three pairwise compatible graphs. -/
theorem union_assoc (hGH : G.Compatible H) (hGK : G.Compatible K) (hHK : H.Compatible K) :
    (hGH.union_compatible hGK hHK).union =
      (hGH.compatible_union hGK hHK).union := by
  apply Graph.ext
  · exact Set.union_assoc V(G) V(H) V(K)
  · intro e x y
    simp only [union_isLink]
    tauto

end Compatible

namespace IsSubgraph

/-- The compatible union of two subgraphs of `K` remains a subgraph of `K`. -/
theorem union_le (hG : G ≤ K) (hH : H ≤ K) : (Compatible.of_le_le hG hH).union ≤ K :=
  (Compatible.of_le_le hG hH).union_le_iff.mpr ⟨hG, hH⟩

end IsSubgraph

end Graph
