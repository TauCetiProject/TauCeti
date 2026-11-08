/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Star
public import TauCeti.Combinatorics.Network.MinimumCut.CutTree
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.PairCutCapacity
import Mathlib.Tactic.Linarith

/-!
# A symmetric submodular cut function not induced by pair capacities

On four vertices, the function `S ↦ min |S| (4 - |S|)` is symmetric and submodular. Every two
distinct vertices have minimum cut value one, so any tree with unit weights is flow-equivalent for
this function. The unit-weight star is a cut tree, but the unit-weight path is not: deleting its
middle edge leaves a side of value two.

This function is not the cut-capacity function of weights on pairs of vertices, even if signed real
weights are allowed. Thus cut trees for symmetric submodular functions are genuinely more general
than graph cut trees, and flow-equivalence records the numerical minimum cut values without
recording their minimizing cuts.
-/

namespace TauCeti.TerminalCut

open Finset SimpleGraph

public section

/-- The balanced cut function on four vertices. -/
def balancedCut (S : Finset (Fin 4)) : ℕ := min #S (4 - #S)

/-- The value of the balanced cut function in terms of the cardinality of the cut. -/
theorem balancedCut_def (S : Finset (Fin 4)) : balancedCut S = min #S (4 - #S) := (rfl)

/-- The balanced cut function vanishes on the empty cut. -/
@[simp]
theorem balancedCut_empty : balancedCut ∅ = 0 := by
  simp [balancedCut_def]

/-- The balanced cut function has value one on a singleton. -/
@[simp]
theorem balancedCut_singleton (x : Fin 4) : balancedCut {x} = 1 := by
  simp [balancedCut_def]

/-- The balanced cut function has value two on a pair of distinct vertices. -/
@[simp]
theorem balancedCut_pair {x y : Fin 4} (hxy : x ≠ y) : balancedCut {x, y} = 2 := by
  simp [balancedCut_def, hxy]

/-- The balanced cut function vanishes on the universal cut. -/
@[simp]
theorem balancedCut_univ : balancedCut (univ : Finset (Fin 4)) = 0 := by
  simp [balancedCut_def]

/-- The balanced cut function is unchanged by exchanging the two sides. -/
@[simp]
theorem balancedCut_compl (S : Finset (Fin 4)) : balancedCut Sᶜ = balancedCut S := by
  have h : #S ≤ 4 := by simpa using card_le_univ S
  simp only [balancedCut, card_compl, Fintype.card_fin]
  omega

/-- The balanced cut function is submodular. -/
theorem isSubmodular_balancedCut : IsSubmodular balancedCut := by
  rw [isSubmodular_def]
  intro S T
  have hS : #S ≤ 4 := by simpa using card_le_univ S
  have hT : #T ≤ 4 := by simpa using card_le_univ T
  have hU : #(S ∪ T) ≤ 4 := by simpa using card_le_univ (S ∪ T)
  have hI : #(S ∩ T) ≤ 4 := by simpa using card_le_univ (S ∩ T)
  have hIS : #(S ∩ T) ≤ #S := card_le_card inter_subset_left
  have hIT : #(S ∩ T) ≤ #T := card_le_card inter_subset_right
  have hSU : #S ≤ #(S ∪ T) := card_le_card subset_union_left
  have hTU : #T ≤ #(S ∪ T) := card_le_card subset_union_right
  have hcard := card_union_add_card_inter S T
  simp only [balancedCut]
  omega

/-- Every distinct pair of vertices has balanced minimum cut value one. -/
theorem pairMinimumValue_balancedCut {s t : Fin 4} (hst : s ≠ t) :
    pairMinimumValue balancedCut s t = 1 := by
  obtain ⟨S, hS⟩ := exists_minimum balancedCut (disjoint_singleton.mpr hst)
  obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
  refine le_antisymm ((pairMinimumValue_le balancedCut (mem_singleton_self s)
    (notMem_singleton.mpr hst.symm)).trans (by simp [balancedCut])) ?_
  have h1 : 0 < #S := card_pos.mpr ⟨s, hs⟩
  have h2 : #S < 4 := by simpa using card_lt_univ_of_notMem ht
  rw [hS.pairMinimumValue_eq, balancedCut]
  omega

/-- Every unit-weight tree on four vertices is flow-equivalent for the balanced cut function. -/
private theorem isFlowEquivalentTree_balanced {T : SimpleGraph (Fin 4)} (hT : T.IsTree) :
    IsFlowEquivalentTree balancedCut T fun _ ↦ 1 where
  isTree := hT
  le_weight s t _ _ _ _ := by
    rcases eq_or_ne s t with rfl | hst
    · simp
    · rw [pairMinimumValue_balancedCut hst]
  exists_weight_eq s t hst p _ := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges
      (by rw [Ne, Walk.edges_eq_nil]; exact Walk.not_nil_of_ne hst)
    exact ⟨e, he, (pairMinimumValue_balancedCut hst).symm⟩

/-- The unit-weight star is a cut tree for the balanced cut function. -/
theorem isCutTree_starGraph_balancedCut :
    IsCutTree balancedCut (starGraph 0) fun _ ↦ 1 := by
  refine ⟨isFlowEquivalentTree_balanced (isTree_starGraph 0), fun u v huv ↦ ?_⟩
  have hbridge : (starGraph (0 : Fin 4)).IsBridge s(u, v) :=
    isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_starGraph 0) huv
  have hleaf : ∀ {a b : Fin 4}, a ≠ 0 → (starGraph 0).edgeSide a b = {a} ∨ b ≠ 0 := by
    intro a b ha
    by_cases hb : b = 0
    · subst hb
      exact .inl (edgeSide_eq_singleton fun y hy ↦ by simp_all [starGraph_adj])
    · exact .inr hb
  -- One end of a star edge is the centre; the side of the leaf is a singleton, and the side of
  -- the centre is its complement.
  have hval : balancedCut ((starGraph 0).edgeSide u v) = 1 := by
    rw [starGraph_adj] at huv
    rcases huv with ⟨hne, rfl | rfl⟩
    · rw [← balancedCut_compl, hbridge.compl_edgeSide (connected_starGraph 0).preconnected,
        (hleaf hne.symm).resolve_right (not_not.mpr rfl), balancedCut_singleton]
    · rw [(hleaf hne).resolve_right (not_not.mpr rfl), balancedCut_singleton]
  rw [isMinimum_singleton_iff_pairMinimumValue_eq, pairMinimumValue_balancedCut huv.ne]
  exact ⟨self_mem_edgeSide _ u v, hbridge.notMem_edgeSide, hval⟩

/-- The unit-weight path is flow-equivalent for the balanced cut function. -/
theorem isFlowEquivalentTree_pathGraph_balancedCut :
    IsFlowEquivalentTree balancedCut (pathGraph 4) fun _ ↦ 1 :=
  isFlowEquivalentTree_balanced (isTree_pathGraph_add_one 3)

/-- The unit-weight path is not a cut tree for the balanced cut function: deleting its middle edge
leaves the side `{0, 1}`, of value two. -/
theorem not_isCutTree_pathGraph_balancedCut :
    ¬IsCutTree balancedCut (pathGraph 4) fun _ ↦ 1 := by
  intro hT
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have hbridge : (pathGraph 4).IsBridge s(1, 2) :=
    isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_pathGraph 4) h12
  have hside : (pathGraph 4).edgeSide 1 2 = {0, 1} := by
    have h0 : (0 : Fin 4) ∈ (pathGraph 4).edgeSide 1 2 :=
      mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
    have h3 : (3 : Fin 4) ∈ (pathGraph 4).edgeSide 2 1 :=
      mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
    have h2 := hbridge.notMem_edgeSide
    ext x
    fin_cases x
    · simpa using h0
    · simp
    · simpa using h2
    · simpa using fun h ↦ Finset.disjoint_left.mp hbridge.disjoint_edgeSide h h3
  have := hT.apply_edgeSide h12
  rw [hside, balancedCut_pair (by decide)] at this
  omega

/-- The balanced cut function is not induced by real pair capacities, even when signed capacities
are allowed. -/
theorem not_exists_pairCutCapacity_eq_balancedCut :
    ¬∃ c : Sym2 (Fin 4) → ℝ, pairCutCapacity c = fun S ↦ (balancedCut S : ℝ) := by
  rintro ⟨c, hcap⟩
  have hzero : ∀ x y, x ≠ y → c s(x, y) = 0 := by
    intro x y hxy
    have h := pairCutCapacity_singleton_add_singleton c hxy
    rw [hcap] at h
    simp [balancedCut, hxy] at h
    linarith
  have hczero : pairCutCapacity c = pairCutCapacity (0 : Sym2 (Fin 4) → ℝ) :=
    pairCutCapacity_eq_of_offDiagonal_eq c 0 fun x y hxy ↦ by
      simp [hzero x y hxy]
  have h := congrFun hcap ({0} : Finset (Fin 4))
  rw [hczero] at h
  rw [pairCutCapacity_zero] at h
  norm_num [balancedCut] at h

/-- The balanced cut function is symmetric submodular. -/
theorem isSymmSubmodular_balancedCut : IsSymmSubmodular balancedCut :=
  ⟨balancedCut_compl, isSubmodular_balancedCut⟩

end

end TauCeti.TerminalCut
