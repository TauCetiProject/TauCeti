/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CutTree
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.Combinatorics.SimpleGraph.PathGraph.Basic

/-!
# Concrete examples of simple-graph cut trees

This file collects finite concrete examples exercising the simple-graph cut-tree and
unit-capacity minimum-cut interface from `TauCeti.Combinatorics.SimpleGraph.Connectivity.CutTree`:

* **Disconnected graph on `Fin 3` (`singleEdgeWithIsolate`):** the graph with single edge `s(0, 1)`
  and isolated vertex `2` forces a zero-weight edge in every unit cut tree and has global edge
  connectivity `0`.
* **Flow-equivalence versus cut-tree witness on `K₄`:** on `⊤ : SimpleGraph (Fin 4)`, the path
  `pathGraph 4` with constant weight `3` is flow-equivalent (matching all pairwise minimum cut
  values), whereas deleting its middle edge `s(1, 2)` leaves `{0, 1}` of cut capacity `4 ≠ 3`, so
  it is not a cut tree (unlike `starGraph r` from `SimpleGraph.isCutTree_starGraph_top`).
* **Multi-level threshold partitions on the diamond graph `K₄ - s(0, 3)` (`diamondGraph`):** the
  weighted path `(pathGraph 4, fun e ↦ if e = s(1, 2) then 3 else 2)` is a unit cut tree exhibiting
  two distinct nonzero local edge-connectivity levels (`2` and `3`), global edge connectivity `2`,
  the threshold-`3` partition separating `{1, 2}` from `0` and `3`, and agreement with `edgeFinset`
  indicator weights.
-/

public section

namespace TauCeti.TerminalCut

open Finset SimpleGraph

/-! ### A disconnected simple graph on `Fin 3` -/

/-- The simple graph on `Fin 3` with single edge `s(0, 1)` and isolated vertex `2`. -/
def singleEdgeWithIsolate : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet {s(0, 1)}

/-- Defining equation for `singleEdgeWithIsolate`. -/
theorem singleEdgeWithIsolate_def :
    singleEdgeWithIsolate = SimpleGraph.fromEdgeSet {s(0, 1)} :=
  (rfl)

/-- Every unit-capacity cut tree for `singleEdgeWithIsolate` contains a zero-weight edge, and the
global edge connectivity of `singleEdgeWithIsolate` is zero. -/
theorem exists_weight_eq_zero_of_isCutTree_singleEdgeWithIsolate
    (T : SimpleGraph (Fin 3)) (w : Sym2 (Fin 3) → ℕ)
    (hT : IsCutTree singleEdgeWithIsolate.unitCutCapacity T w) :
    (∃ e ∈ T.edgeSet, w e = 0) ∧ singleEdgeWithIsolate.edgeConnectivity = 0 := by
  have hnot : ¬singleEdgeWithIsolate.Preconnected := by
    intro hconn
    obtain ⟨p⟩ := hconn 2 0
    cases p with
    | cons hadj _ =>
      simp only [singleEdgeWithIsolate, fromEdgeSet_adj, Set.mem_singleton_iff] at hadj
      rcases Sym2.eq_iff.mp hadj.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
  have hex : ∃ e ∈ T.edgeSet, w e = 0 := by
    by_contra h
    push Not at h
    exact hnot (hT.toIsFlowEquivalentTree.simpleGraph_preconnected_iff_forall_weight_pos.mpr
      fun e he ↦ Nat.pos_of_ne_zero (h e he))
  refine ⟨hex, le_antisymm ?_ bot_le⟩
  obtain ⟨e, he, hwe⟩ := hex
  simpa [hwe] using hT.toIsFlowEquivalentTree.simpleGraph_edgeConnectivity_le_weight he

/-! ### Separating flow-equivalent trees from cut trees on `K₄` -/

/-- On the complete graph `K₄`, the path `pathGraph 4` with constant weight `3` is flow-equivalent
for unit cut capacity, because every pair of distinct vertices has minimum cut value `3`. -/
theorem isFlowEquivalentTree_pathGraph_four_top :
    IsFlowEquivalentTree (⊤ : SimpleGraph (Fin 4)).unitCutCapacity
      (pathGraph 4) (fun _ ↦ 3) where
  isTree := isTree_pathGraph_add_one 3
  le_weight s t _ _ _ _ := by
    rcases eq_or_ne s t with rfl | hst
    · simp
    · rw [pairMinimumValue_unitCutCapacity_top hst]
      simp
  exists_weight_eq s t hst p _ := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges
      (by rw [Ne, Walk.edges_eq_nil]; exact Walk.not_nil_of_ne hst)
    refine ⟨e, he, ?_⟩
    rw [pairMinimumValue_unitCutCapacity_top hst]
    simp

/-- On `K₄`, `pathGraph 4` with constant weight `3` is not a cut tree: deleting its middle edge
`s(1, 2)` leaves the side `{0, 1}`, across which four edges of `K₄` cross. -/
theorem not_isCutTree_pathGraph_four_top :
    ¬IsCutTree (⊤ : SimpleGraph (Fin 4)).unitCutCapacity
      (pathGraph 4) (fun _ ↦ 3) := by
  intro hT
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have happly := hT.apply_edgeSide h12
  rw [edgeSide_pathGraph_eq_Iic (by decide), unitCutCapacity_top] at happly
  have hcard : #(Finset.Iic (1 : Fin 4)) = 2 := by decide
  rw [hcard, Fintype.card_fin] at happly
  omega

/-! ### The diamond graph `K₄ - s(0, 3)`: multi-level threshold partitions -/

/-- The diamond graph obtained by deleting the edge `s(0, 3)` from `K₄`. Vertices `0` and `3`
have degree `2`, while `1` and `2` have degree `3` and local edge connectivity `3`. -/
def diamondGraph : SimpleGraph (Fin 4) :=
  (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 3)}

/-- Defining equation for `diamondGraph`. -/
theorem diamondGraph_def :
    diamondGraph = (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 3)} :=
  (rfl)

private theorem diamondGraph_cut (S : Finset (Fin 4)) [Decidable (s((0 : Fin 4), 3).Crosses S)] :
    diamondGraph.unitCutCapacity S +
        (if s((0 : Fin 4), 3).Crosses (S : Set (Fin 4)) then 1 else 0) =
      #S * (4 - #S) := by
  have he : s((0 : Fin 4), 3) ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet := by decide
  have h := unitCutCapacity_deleteEdges_singleton (⊤ : SimpleGraph (Fin 4)) he S
  rw [unitCutCapacity_top, Fintype.card_fin] at h
  exact h

private theorem diamondGraph_cut_ge_two {S : Finset (Fin 4)} {s t : Fin 4}
    (hs : s ∈ S) (ht : t ∉ S) :
    2 ≤ diamondGraph.unitCutCapacity S := by
  classical
  have h := diamondGraph_cut S
  have hpos : 1 ≤ #S := Finset.one_le_card.mpr ⟨s, hs⟩
  have hlt : #S < 4 := by simpa using Finset.card_lt_univ_of_notMem ht
  have hprod : 3 ≤ #S * (4 - #S) := by
    have hcases : #S = 1 ∨ #S = 2 ∨ #S = 3 := by omega
    rcases hcases with hS | hS | hS <;> simp [hS]
  split_ifs at h <;> omega

private theorem diamondGraph_cut_singleton_zero :
    diamondGraph.unitCutCapacity {0} = 2 := by
  classical
  have h := diamondGraph_cut {0}
  have hcross : s((0 : Fin 4), 3).Crosses (({0} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  simp only [hcross, ↓reduceIte, card_singleton] at h
  omega

private theorem diamondGraph_cut_singleton_three :
    diamondGraph.unitCutCapacity {3} = 2 := by
  classical
  have h := diamondGraph_cut {3}
  have hcross : s((0 : Fin 4), 3).Crosses (({3} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  simp only [hcross, ↓reduceIte, card_singleton] at h
  omega

private theorem diamondGraph_cut_pair_zero_one :
    diamondGraph.unitCutCapacity {0, 1} = 3 := by
  classical
  have h := diamondGraph_cut {0, 1}
  have hcross : s((0 : Fin 4), 3).Crosses (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  have hcard : #({0, 1} : Finset (Fin 4)) = 2 := by decide
  simp only [hcross, ↓reduceIte, hcard] at h
  omega

private theorem diamondGraph_minCut_zero_one :
    pairMinimumValue diamondGraph.unitCutCapacity 0 1 = 2 := by
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue diamondGraph.unitCutCapacity 0 1 ≤ diamondGraph.unitCutCapacity {0} :=
        pairMinimumValue_le _ (mem_singleton_self 0) (by decide)
      _ = 2 := diamondGraph_cut_singleton_zero
  · obtain ⟨S, hS⟩ := exists_minimum diamondGraph.unitCutCapacity
      (disjoint_singleton.mpr (by decide : (0 : Fin 4) ≠ 1))
    obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    exact diamondGraph_cut_ge_two hs ht

private theorem diamondGraph_minCut_two_three :
    pairMinimumValue diamondGraph.unitCutCapacity 2 3 = 2 := by
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue diamondGraph.unitCutCapacity 2 3 ≤
          diamondGraph.unitCutCapacity ({3}ᶜ : Finset (Fin 4)) :=
        pairMinimumValue_le _ (by decide) (by decide)
      _ = diamondGraph.unitCutCapacity {3} := diamondGraph.unitCutCapacity_compl {3}
      _ = 2 := diamondGraph_cut_singleton_three
  · obtain ⟨S, hS⟩ := exists_minimum diamondGraph.unitCutCapacity
      (disjoint_singleton.mpr (by decide : (2 : Fin 4) ≠ 3))
    obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    exact diamondGraph_cut_ge_two hs ht

private theorem diamondGraph_minCut_one_two :
    pairMinimumValue diamondGraph.unitCutCapacity 1 2 = 3 := by
  classical
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue diamondGraph.unitCutCapacity 1 2 ≤ diamondGraph.unitCutCapacity {0, 1} :=
        pairMinimumValue_le _ (by decide) (by decide)
      _ = 3 := diamondGraph_cut_pair_zero_one
  · obtain ⟨S, hS⟩ := exists_minimum diamondGraph.unitCutCapacity
      (disjoint_singleton.mpr (by decide : (1 : Fin 4) ≠ 2))
    obtain ⟨h1, h2⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    have h := diamondGraph_cut S
    have hpos : 1 ≤ #S := Finset.one_le_card.mpr ⟨1, h1⟩
    have hlt : #S < 4 := by simpa using Finset.card_lt_univ_of_notMem h2
    by_cases hcross : s((0 : Fin 4), 3).Crosses (S : Set (Fin 4))
    · simp only [hcross, ↓reduceIte] at h
      have hcard2 : #S = 2 := by
        rcases Sym2.crosses_mk_iff.mp hcross with ⟨h0, h3⟩ | ⟨h3, h0⟩
        · have hsub : S = {0, 1} := by
            ext x; fin_cases x <;> simp_all
          rw [hsub]; decide
        · have hsub : S = {1, 3} := by
            ext x; fin_cases x <;> simp_all
          rw [hsub]; decide
      rw [hcard2] at h
      omega
    · simp only [hcross, ↓reduceIte, add_zero] at h
      have hprod : 3 ≤ #S * (4 - #S) := by
        have hcases : #S = 1 ∨ #S = 2 ∨ #S = 3 := by omega
        rcases hcases with hS | hS | hS <;> simp [hS]
      omega

/-- On the diamond graph `K₄ - s(0, 3)`, the path `pathGraph 4` with middle weight `3` and leaf
weights `2` is a unit cut tree. -/
theorem isCutTree_pathGraph_diamondGraph :
    IsCutTree diamondGraph.unitCutCapacity
      (pathGraph 4) (fun e ↦ if e = s(1, 2) then 3 else 2) := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_pathGraph 4)
  have hpre : (pathGraph 4).Preconnected := (isTree_pathGraph_add_one 3).connected.preconnected
  have hcomm := fun u v ↦ pairMinimumValue_comm diamondGraph.unitCutCapacity_compl u v
  have hadj : ∀ {u v : Fin 4}, (pathGraph 4).Adj u v →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨
      (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [pathGraph_adj] at huv ⊢
  have hIic0 : Finset.Iic (0 : Fin 4) = {0} := by decide
  have hIic1 : Finset.Iic (1 : Fin 4) = {0, 1} := by decide
  have hIci3 : Finset.Ici (3 : Fin 4) = {3} := by decide
  refine IsCutTree.of_isMinimum_edgeSide (isTree_pathGraph_add_one 3) ?_ ?_
  · intro u v huv
    rw [isMinimum_singleton_iff_pairMinimumValue_eq]
    refine ⟨self_mem_edgeSide _ u v, (hbr huv).notMem_edgeSide, ?_⟩
    rcases hadj huv with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [edgeSide_pathGraph_eq_Iic (by decide), hIic0, diamondGraph_cut_singleton_zero,
        diamondGraph_minCut_zero_one]
    · rw [← diamondGraph.unitCutCapacity_compl, (hbr huv).compl_edgeSide hpre,
        edgeSide_pathGraph_eq_Iic (by decide), hIic0, diamondGraph_cut_singleton_zero, hcomm 1 0,
        diamondGraph_minCut_zero_one]
    · rw [edgeSide_pathGraph_eq_Iic (by decide), hIic1, diamondGraph_cut_pair_zero_one,
        diamondGraph_minCut_one_two]
    · rw [← diamondGraph.unitCutCapacity_compl, (hbr huv).compl_edgeSide hpre,
        edgeSide_pathGraph_eq_Iic (by decide), hIic1, diamondGraph_cut_pair_zero_one, hcomm 2 1,
        diamondGraph_minCut_one_two]
    · rw [← diamondGraph.unitCutCapacity_compl, (hbr huv).compl_edgeSide hpre,
        edgeSide_pathGraph_eq_Ici (by decide), hIci3, diamondGraph_cut_singleton_three,
        diamondGraph_minCut_two_three]
    · rw [edgeSide_pathGraph_eq_Ici (by decide), hIci3, diamondGraph_cut_singleton_three,
        hcomm 3 2, diamondGraph_minCut_two_three]
  · intro u v huv
    rcases hadj huv with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [diamondGraph_minCut_zero_one]; decide
    · rw [hcomm 1 0, diamondGraph_minCut_zero_one]; decide
    · rw [diamondGraph_minCut_one_two]; decide
    · rw [hcomm 2 1, diamondGraph_minCut_one_two]; decide
    · rw [diamondGraph_minCut_two_three]; decide
    · rw [hcomm 3 2, diamondGraph_minCut_two_three]; decide

/-- On the diamond graph `K₄ - s(0, 3)`, the cut tree `isCutTree_pathGraph_diamondGraph` exhibits
two distinct nonzero local edge-connectivity levels (`2` and `3`), yields global edge connectivity
`2`, realizes the threshold-`3` partition by deleting edges of weight `< 3`, and matches the
`edgeFinset` indicator formulation. -/
theorem diamondGraph_edgeConnectivity_and_threshold_three :
    diamondGraph.edgeConnectivity = 2 ∧
    diamondGraph.IsEdgeConnected 2 ∧
    ¬diamondGraph.IsEdgeConnected 3 ∧
    diamondGraph.edgeReachability 1 2 = 3 ∧
    diamondGraph.edgeReachability 0 1 = 2 ∧
    diamondGraph.IsEdgeReachable 3 1 2 ∧
    ¬diamondGraph.IsEdgeReachable 3 0 1 ∧
    ¬diamondGraph.IsEdgeReachable 4 1 2 ∧
    ((pathGraph 4).deleteEdges {e | (if e = s(1, 2) then 3 else 2) < 3}).Reachable 1 2 ∧
    ¬((pathGraph 4).deleteEdges {e | (if e = s(1, 2) then 3 else 2) < 3}).Reachable 0 1 ∧
    (∀ [Fintype diamondGraph.edgeSet],
      diamondGraph.IsEdgeReachable (3 : ℕ) 1 2 ↔
        3 ≤ pairMinimumValue
          (pairCutCapacity fun e ↦
            if e ∈ diamondGraph.edgeFinset then (1 : ℕ) else 0) 1 2) := by
  have hT := isCutTree_pathGraph_diamondGraph.toIsFlowEquivalentTree
  have hne : s((0 : Fin 4), 1) ≠ s(1, 2) := by decide
  have h2 : diamondGraph.IsEdgeConnected 2 := by
    rw [hT.simpleGraph_isEdgeConnected_iff_forall_le_weight]
    intro e _
    split_ifs <;> decide
  have hnot3 : ¬diamondGraph.IsEdgeConnected 3 := by
    rw [hT.simpleGraph_isEdgeConnected_iff_forall_le_weight]
    push Not
    refine ⟨s(0, 1), by simp [pathGraph_adj], ?_⟩
    simp only [hne, ↓reduceIte]
    exact_mod_cast (by decide : 2 < 3)
  have hec : diamondGraph.edgeConnectivity = 2 := by
    refine le_antisymm ?_ (diamondGraph.isEdgeConnected_iff_le_edgeConnectivity.mp h2)
    have h01 : s((0 : Fin 4), 1) ∈ (pathGraph 4).edgeSet := by simp [pathGraph_adj]
    simpa [hne] using hT.simpleGraph_edgeConnectivity_le_weight h01
  have hr12 : diamondGraph.edgeReachability 1 2 = 3 := by
    rw [diamondGraph.edgeReachability_eq_pairMinimumValue_unitCutCapacity
      (by decide : (1 : Fin 4) ≠ 2), diamondGraph_minCut_one_two]
    rfl
  have hr01 : diamondGraph.edgeReachability 0 1 = 2 := by
    rw [diamondGraph.edgeReachability_eq_pairMinimumValue_unitCutCapacity
      (by decide : (0 : Fin 4) ≠ 1), diamondGraph_minCut_zero_one]
    rfl
  have h12_3 : diamondGraph.IsEdgeReachable 3 1 2 :=
    diamondGraph.isEdgeReachable_iff_le_edgeReachability.mpr (by simp [hr12])
  have h01_3 : ¬diamondGraph.IsEdgeReachable 3 0 1 := by
    rw [diamondGraph.isEdgeReachable_iff_le_edgeReachability, hr01]
    decide
  have h12_4 : ¬diamondGraph.IsEdgeReachable 4 1 2 := by
    rw [diamondGraph.isEdgeReachable_iff_le_edgeReachability, hr12]
    decide
  refine ⟨hec, h2, hnot3, hr12, hr01, h12_3, h01_3, h12_4,
    (hT.reachable_deleteEdges_iff_simpleGraph_isEdgeReachable 3).mpr h12_3,
    mt (hT.reachable_deleteEdges_iff_simpleGraph_isEdgeReachable 3).mp h01_3, fun {_} ↦ ?_⟩
  rw [← diamondGraph.indicator_edgeSet_eq_ite_mem_edgeFinset (fun _ ↦ (1 : ℕ)),
    ← diamondGraph.unitCutCapacity_eq_pairCutCapacity,
    diamondGraph.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity
      (by decide : (1 : Fin 4) ≠ 2) (3 : ℕ),
    Nat.cast_le]

end TauCeti.TerminalCut
