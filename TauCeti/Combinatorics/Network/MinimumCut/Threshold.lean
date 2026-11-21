/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.CutTree

/-!
# Threshold components of flow-equivalent trees

Let `T` be a flow-equivalent tree for a set function `f`, with edge weights `w`.  At a threshold
`k`, delete the edges of weight below `k`.  The remaining connected components are exactly the
equivalence classes for

`s = t ∨ k ≤ pairMinimumValue f s t`.

The reachability characterization is proved in
`IsFlowEquivalentTree.reachable_deleteEdges_iff`.  This file packages its right-hand side as a
setoid, identifies the quotient with the connected components of the threshold graph, and gives
the corresponding class-membership formula.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551–570.
-/

public section

namespace TauCeti.TerminalCut

open Finset SimpleGraph

variable {V K : Type*} [Finite V] [Zero K] [LinearOrder K]
variable {f : Finset V → K} {T : SimpleGraph V} {w : Sym2 V → K}

/-- Two vertices are related at threshold `k` when they are equal or their minimum cut value is at
least `k`.  The equality alternative is necessary because `pairMinimumValue f s s = 0`. -/
def ThresholdRelated (f : Finset V → K) (k : K) (s t : V) : Prop :=
  s = t ∨ k ≤ pairMinimumValue f s t

namespace IsFlowEquivalentTree

/-- Threshold relatedness is precisely reachability after deleting the tree edges lighter than
the threshold. -/
theorem thresholdRelated_iff_reachable (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    ThresholdRelated f k s t ↔ (T.deleteEdges {e | w e < k}).Reachable s t :=
  (hT.reachable_deleteEdges_iff k).symm

/-- Threshold relatedness is an equivalence relation. -/
theorem thresholdRelated_equivalence (hT : IsFlowEquivalentTree f T w) (k : K) :
    Equivalence (ThresholdRelated f k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact Or.inl rfl
  · intro s t hst
    rw [hT.thresholdRelated_iff_reachable k] at hst ⊢
    exact hst.symm
  · intro s t u hst htu
    rw [hT.thresholdRelated_iff_reachable k] at hst htu ⊢
    exact hst.trans htu

/-- The equivalence relation whose classes are the threshold components. -/
def thresholdSetoid (hT : IsFlowEquivalentTree f T w) (k : K) : Setoid V where
  r := ThresholdRelated f k
  iseqv := hT.thresholdRelated_equivalence k

@[simp]
theorem thresholdSetoid_rel (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    hT.thresholdSetoid k s t ↔ s = t ∨ k ≤ pairMinimumValue f s t :=
  Iff.rfl

/-- The abstract type of threshold classes. -/
def ThresholdComponent (hT : IsFlowEquivalentTree f T w) (k : K) :=
  Quotient (hT.thresholdSetoid k)

/-- The threshold class containing a vertex. -/
def thresholdComponentMk (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    hT.ThresholdComponent k :=
  Quotient.mk _ v

@[simp]
theorem thresholdComponentMk_eq_iff (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    hT.thresholdComponentMk k s = hT.thresholdComponentMk k t ↔
      s = t ∨ k ≤ pairMinimumValue f s t :=
  Quotient.eq'

/-- Threshold classes are canonically the connected components of the threshold graph. -/
def thresholdComponentEquiv (hT : IsFlowEquivalentTree f T w) (k : K) :
    hT.ThresholdComponent k ≃ (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  show Quotient (hT.thresholdSetoid k) ≃
    Quotient (T.deleteEdges {e | w e < k}).reachableSetoid from
    Quotient.congrRight fun s t ↦ hT.thresholdRelated_iff_reachable k s t

@[simp]
theorem thresholdComponentEquiv_apply_mk (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    hT.thresholdComponentEquiv k (hT.thresholdComponentMk k v) =
      (T.deleteEdges {e | w e < k}).connectedComponentMk v := by
  exact Quotient.congr_mk (Equiv.refl V)
    (fun s t ↦ hT.thresholdRelated_iff_reachable k s t) v

@[simp]
theorem thresholdComponentEquiv_symm_apply_mk
    (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    (hT.thresholdComponentEquiv k).symm
        ((T.deleteEdges {e | w e < k}).connectedComponentMk v) =
      hT.thresholdComponentMk k v := by
  apply (hT.thresholdComponentEquiv k).injective
  simp

/-- Two vertices determine the same connected component of the threshold graph exactly when they
are equal or their minimum cut value is at least the threshold. -/
theorem connectedComponentMk_threshold_eq_iff
    (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    (T.deleteEdges {e | w e < k}).connectedComponentMk s =
        (T.deleteEdges {e | w e < k}).connectedComponentMk t ↔
      s = t ∨ k ≤ pairMinimumValue f s t := by
  rw [ConnectedComponent.eq, ← hT.thresholdRelated_iff_reachable]
  rfl

/-- Membership in the threshold component of `s` is governed by the threshold minimum-cut
relation. -/
theorem mem_thresholdComponent_iff (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    t ∈ ((T.deleteEdges {e | w e < k}).connectedComponentMk s).supp ↔
      s = t ∨ k ≤ pairMinimumValue f s t := by
  rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, reachable_comm,
    hT.reachable_deleteEdges_iff]

/-- The abstract threshold quotient and the graph's connected-component type have the same
cardinality. -/
theorem natCard_thresholdComponent_eq (hT : IsFlowEquivalentTree f T w) (k : K) :
    Nat.card (hT.ThresholdComponent k) =
      Nat.card (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  Nat.card_congr (hT.thresholdComponentEquiv k)

end IsFlowEquivalentTree

end TauCeti.TerminalCut
