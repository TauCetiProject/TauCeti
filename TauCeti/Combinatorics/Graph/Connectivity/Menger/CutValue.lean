/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeConnectivity
public import Mathlib.Data.Set.Card
import TauCeti.Combinatorics.SimpleGraph.Connectivity.CutCapacity

/-!
# Edge reachability and unit-capacity minimum cuts

Menger's theorem identifies the number of edge-disjoint paths between two vertices with the
least size of an edge separator. This file gives the equivalent cut-value interface: assigning
unit capacity to every actual edge makes the minimum cut value between two distinct actual
vertices equal to their local edge reachability. Parallel edges contribute separately, while
loops never contribute to a cut.

The threshold form is useful without choosing a minimum cut. The numerical form lets results about
minimum cut values, such as cut trees, apply to the deletion-based invariant.

For a simple graph `G : SimpleGraph V`, equating local edge reachability with minimum
`G.unitCutCapacity` cut values directly on `V` yields threshold and numerical characterizations of
`G.IsEdgeReachable`, `G.edgeReachability`, `G.IsEdgeConnected`, and `G.edgeConnectivity`, together
with complete-graph values.

## Main results

* `Graph.isEdgeReachable_iff_le_pairMinimumValue`: edge reachability at threshold `k` is
  equivalent to `k` being at most the minimum unit cut value.
* `Graph.edgeReachability_eq_pairMinimumValue`: the numerical local edge reachability is the
  minimum unit cut value, viewed in `ℕ∞`.
* `Graph.edgeReachability_eq_pairMinimumValue_pairCapacity`: aggregating parallel unit edges by
  their unordered endpoint pairs preserves this value.
* `SimpleGraph.edgeReachability_eq_pairMinimumValue_unitCutCapacity`,
  `SimpleGraph.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity`, and
  `SimpleGraph.edgeConnectivity_eq_iInf_pairMinimumValue_unitCutCapacity`: native simple-graph local
  edge reachability and global edge connectivity in terms of `G.unitCutCapacity` minimum cut values.
* `SimpleGraph.edgeReachability_top` and `SimpleGraph.edgeConnectivity_top`: local edge
  reachability and global edge connectivity `|V| - 1` of complete graphs.

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

/-- Local edge reachability is the pair minimum value extended to `ℕ∞`, with value `⊤` on
the diagonal. -/
theorem edgeReachability_eq_iInf_pairMinimumValue (G : Graph α β)
    [Finite V(G)] [Fintype E(G)] (s t : V(G)) :
    G.edgeReachability s t =
      ⨅ (_ : s ≠ t),
        ((TerminalCut.pairMinimumValue (G.edgeCutCapacity fun _ ↦ (1 : ℕ)) s t : ℕ) : ℕ∞) := by
  by_cases hst : s = t
  · subst t
    simp [G.edgeReachability_self s.property]
  · simp [hst, G.edgeReachability_eq_pairMinimumValue hst]

/-- Aggregating the unit capacities of parallel edges by their unordered pairs does not change
the minimum cut value computing local edge reachability. The aggregated capacity of a pair is its
edge multiplicity, rather than merely the adjacency indicator. -/
theorem edgeReachability_eq_pairMinimumValue_pairCapacity [Fintype V(G)] [Fintype E(G)]
    {s t : V(G)} (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TerminalCut.pairMinimumValue
        (pairCutCapacity (G.pairCapacity fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) := by
  rw [G.pairCutCapacity_pairCapacity (fun _ ↦ (1 : ℕ)),
    edgeReachability_eq_pairMinimumValue hst]

end Graph

open scoped Graph

namespace SimpleGraph

variable {V : Type*}

/-- For distinct vertices, simple-graph edge reachability is the minimum unit cut value, viewed
in `ℕ∞`. -/
theorem edgeReachability_eq_pairMinimumValue_unitCutCapacity [Finite V] (G : SimpleGraph V)
    {s t : V} (hst : s ≠ t) :
    G.edgeReachability s t =
      ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  let _ := Fintype.ofFinite V
  let e := G.ofSimpleGraphVertexEquiv
  have hmap (S : Finset V) :
      S.map e.toEmbedding = G.toOfSimpleGraphFinset S := by
    exact (G.toOfSimpleGraphFinset_eq_map S).symm
  have he (S : Finset V) :
      (Graph.ofSimpleGraph G).edgeCutCapacity (fun _ ↦ (1 : ℕ))
          (S.map e.toEmbedding) = G.unitCutCapacity S := by
    rw [hmap]
    exact (G.unitCutCapacity_eq_edgeCutCapacity S).symm
  have hst' : e s ≠ e t := e.injective.ne hst
  have hreach :=
    (Graph.ofSimpleGraph G).edgeReachability_eq_pairMinimumValue (s := e s) (t := e t) hst'
  have hmin := TerminalCut.pairMinimumValue_map G.unitCutCapacity e
    ((Graph.ofSimpleGraph G).edgeCutCapacity fun _ ↦ (1 : ℕ)) he s t
  simp only [e, Graph.edgeReachability_ofSimpleGraph,
    G.ofSimpleGraphVertexEquiv_apply_val] at hreach
  exact hreach.trans (congrArg (↑· : ℕ → ℕ∞) hmin)

/-- Simple-graph edge reachability is the unit pair minimum value extended to `ℕ∞`, with
value `⊤` on the diagonal. -/
theorem edgeReachability_eq_iInf_pairMinimumValue_unitCutCapacity [Finite V]
    (G : SimpleGraph V) (s t : V) :
    G.edgeReachability s t =
      ⨅ (_ : s ≠ t), ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  by_cases hst : s = t
  · subst t
    simp
  · simp [hst, G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]

section

variable (G : SimpleGraph V)

/-- For distinct vertices of a finite simple graph, local edge reachability at threshold
`k : ℕ∞` holds exactly when `k` is at most the minimum unit cut value between `s` and `t`. -/
theorem isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity [Finite V] {s t : V}
    (hst : s ≠ t) (k : ℕ∞) :
    G.IsEdgeReachable k s t ↔
      k ≤ ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  rw [G.isEdgeReachable_iff_le_edgeReachability,
    G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]

/-- Distinct vertices have minimum unit cut value zero exactly when they are not reachable. -/
theorem pairMinimumValue_unitCutCapacity_eq_zero_iff [Finite V] {s t : V} (hst : s ≠ t) :
    TerminalCut.pairMinimumValue G.unitCutCapacity s t = 0 ↔ ¬G.Reachable s t := by
  rw [← SimpleGraph.isEdgeReachable_one,
    G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst 1]
  norm_cast
  omega

/-- Every edge separator between `s` and `t` has cardinality at least their minimum unit cut
value. -/
theorem pairMinimumValue_unitCutCapacity_le_encard_of_not_reachable [Finite V]
    {s t : V} {F : Set (Sym2 V)} (hF : ¬(G.deleteEdges F).Reachable s t) :
    ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) ≤ F.encard := by
  rcases eq_or_ne s t with rfl | hst
  · exact (hF .rfl).elim
  · by_contra hlt
    push Not at hlt
    have hreach : G.IsEdgeReachable
        ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) s t :=
      (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst _).mpr le_rfl
    exact hF (hreach hlt)

/-- On the complete graph `⊤` over a finite vertex type, any two distinct vertices have local edge
reachability `|V| - 1`. -/
theorem edgeReachability_top [Fintype V] {s t : V} (hst : s ≠ t) :
    (⊤ : SimpleGraph V).edgeReachability s t = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  rw [edgeReachability_eq_pairMinimumValue_unitCutCapacity _ hst,
    pairMinimumValue_unitCutCapacity_top hst]

/-- The global edge connectivity of the complete graph on a finite nontrivial vertex type `V` is
`|V| - 1`. -/
theorem edgeConnectivity_top [Fintype V] [Nontrivial V] :
    (⊤ : SimpleGraph V).edgeConnectivity = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  refine le_antisymm ?_ ?_
  · exact ((⊤ : SimpleGraph V).edgeConnectivity_le_edgeReachability u v).trans_eq
      (edgeReachability_top huv)
  · rw [(⊤ : SimpleGraph V).edgeConnectivity_eq_iInf_edgeReachability]
    refine le_iInf fun x ↦ le_iInf fun y ↦ ?_
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · exact (edgeReachability_top hxy).ge

/-- A finite simple graph is `k`-edge-connected iff every pair of distinct vertices has minimum
unit cut value at least `k`. -/
theorem isEdgeConnected_iff_forall_le_pairMinimumValue_unitCutCapacity [Finite V] (k : ℕ∞) :
    G.IsEdgeConnected k ↔
      ∀ s t : V, s ≠ t →
        k ≤ ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  constructor
  · intro h s t hst
    exact (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst k).mp (h s t)
  · intro h s t
    rcases eq_or_ne s t with rfl | hst
    · exact .rfl
    · exact (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst k).mpr (h s t hst)

/-- The global edge connectivity of a finite simple graph is the infimum of pairwise minimum unit
cut values over distinct vertices. On empty and singleton types both sides are `⊤`. -/
theorem edgeConnectivity_eq_iInf_pairMinimumValue_unitCutCapacity [Finite V] :
    G.edgeConnectivity =
      ⨅ (s : V) (t : V) (_ : s ≠ t),
        ((TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  rw [G.edgeConnectivity_eq_iInf_edgeReachability]
  simp_rw [G.edgeReachability_eq_iInf_pairMinimumValue_unitCutCapacity]

end

end SimpleGraph
