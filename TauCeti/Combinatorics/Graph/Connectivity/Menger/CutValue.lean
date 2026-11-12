/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import TauCeti.Combinatorics.Network.MinimumCut.Basic
public import Mathlib.Data.Set.Card

/-!
# Edge reachability and unit-capacity minimum cuts

Menger's theorem identifies the number of edge-disjoint paths between two vertices with the
least size of an edge separator. This file gives the equivalent cut-value interface: assigning
unit capacity to every actual edge makes the minimum cut value between two distinct actual
vertices equal to their local edge reachability. Parallel edges contribute separately, while
loops never contribute to a cut.

The threshold form is useful without choosing a minimum cut. The numerical form lets results about
minimum cut values, such as cut trees, apply to the deletion-based invariant.

## Main results

* `Graph.isEdgeReachable_iff_le_pairMinimumValue`: edge reachability at threshold `k` is
  equivalent to `k` being at most the minimum unit cut value.
* `Graph.edgeReachability_eq_pairMinimumValue`: the numerical local edge reachability is the
  minimum unit cut value, viewed in `ℕ∞`.
* `Graph.edgeReachability_eq_pairMinimumValue_pairCapacity`: aggregating parallel unit edges by
  their unordered endpoint pairs preserves this value.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

open Finset TauCeti

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- If deleting an edge set separates two actual vertices, then the edge set contains the
boundary of the side reachable from the first vertex. -/
private theorem exists_edgeCut_subset_of_not_reachable [Finite V(G)] {s t : V(G)} {F : Set β}
    (hF : ¬(G.deleteEdges F).Reachable s t) :
    ∃ S : Finset V(G), s ∈ S ∧ t ∉ S ∧
      G.edgeCut (Subtype.val '' (S : Set V(G))) ⊆ F := by
  classical
  let _ := Fintype.ofFinite V(G)
  let S : Finset V(G) := {v | (G.deleteEdges F).Reachable s v}
  have hs : s ∈ S := by
    simp only [S, mem_filter, mem_univ, true_and]
    exact .refl (by simp)
  have ht : t ∉ S := by
    simpa only [S, mem_filter, mem_univ, true_and] using hF
  have hS : Subtype.val '' (S : Set V(G)) =
      {v | (G.deleteEdges F).Reachable s v} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : (G.deleteEdges F).Reachable s w := by simpa [S] using hw
      exact hw'
    · intro hv
      exact ⟨⟨v, by simpa using hv.right_mem⟩, by simpa [S] using hv, rfl⟩
  refine ⟨S, hs, ht, ?_⟩
  rw [hS]
  exact G.edgeCut_setOf_reachable_deleteEdges_subset F s

/-- For distinct actual vertices of a finite multigraph, edge reachability at threshold `k` is
equivalent to `k` being at most the minimum cut value when every edge has capacity one. -/
theorem isEdgeReachable_iff_le_pairMinimumValue [Finite V(G)] [Fintype E(G)]
    {s t : V(G)} (hst : s ≠ t) (k : ℕ) :
    G.IsEdgeReachable k s t ↔
      k ≤ TerminalCut.pairMinimumValue (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) s t := by
  classical
  let _ := Fintype.ofFinite V(G)
  constructor
  · intro hk
    obtain ⟨S, hS⟩ := TerminalCut.exists_minimum
      (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) (disjoint_singleton.mpr hst)
    obtain ⟨hs, ht⟩ := TerminalCut.isAdmissible_singleton.mp hS.admissible
    let C := G.edgeCut (Subtype.val '' (S : Set V(G)))
    have hCfin : C.Finite := (Set.toFinite E(G)).subset G.edgeCut_subset_edgeSet
    have hle : (k : ℕ∞) ≤ C.encard := not_lt.mp fun hlt ↦ by
      have hs' : (s : α) ∈ Subtype.val '' (S : Set V(G)) := ⟨s, hs, rfl⟩
      have ht' : (t : α) ∉ Subtype.val '' (S : Set V(G)) := by
        rintro ⟨w, hw, hwt⟩
        exact ht (Subtype.ext hwt ▸ hw)
      exact G.not_reachable_deleteEdges_edgeCut hs' ht'
        ((isEdgeReachable_def.mp hk) (F := C) hlt)
    rw [← hCfin.cast_ncard_eq, Nat.cast_le] at hle
    rwa [hS.pairMinimumValue_eq, edgeCutCapacity_one]
  · intro hk
    rw [isEdgeReachable_def]
    intro F hFk
    by_contra hF
    have hFfin : F.Finite := Set.encard_ne_top_iff.mp
      (ne_top_of_lt (hFk.trans (ENat.natCast_lt_top k)))
    obtain ⟨S, hs, ht, hSF⟩ := exists_edgeCut_subset_of_not_reachable hF
    have hmin :
        TerminalCut.pairMinimumValue (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) s t ≤ F.ncard :=
      (TerminalCut.pairMinimumValue_le _ hs ht).trans <| by
        rw [edgeCutCapacity_one]
        exact Set.ncard_le_ncard hSF hFfin
    have hFcard : F.ncard < k := by
      rw [← Nat.cast_lt (α := ℕ∞), hFfin.cast_ncard_eq]
      exact hFk
    exact (not_lt_of_ge (hk.trans hmin)) hFcard

/-- For distinct actual vertices of a finite multigraph, local edge reachability is its minimum
unit-capacity cut value, viewed in `ℕ∞`. -/
theorem edgeReachability_eq_pairMinimumValue [Finite V(G)] [Fintype E(G)] {s t : V(G)}
    (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TerminalCut.pairMinimumValue (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) s t : ℕ) : ℕ∞) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [← isEdgeReachable_iff_le_edgeReachability,
    isEdgeReachable_iff_le_pairMinimumValue hst, Nat.cast_le]

/-- Aggregating the unit capacities of parallel edges by their unordered pairs does not change
the minimum cut value computing local edge reachability. The aggregated capacity of a pair is its
edge multiplicity, rather than merely the adjacency indicator. -/
theorem edgeReachability_eq_pairMinimumValue_pairCapacity [Fintype V(G)] [Fintype E(G)]
    {s t : V(G)} (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TerminalCut.pairMinimumValue
        (pairCutCapacity (G.pairCapacity fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) := by
  have hcut : pairCutCapacity (G.pairCapacity fun _ ↦ (1 : ℕ)) =
      G.edgeCutCapacity fun _ ↦ (1 : ℕ) :=
    funext fun S ↦ G.pairCutCapacity_pairCapacity (fun _ ↦ (1 : ℕ)) S
  rw [hcut, edgeReachability_eq_pairMinimumValue hst]

end Graph
