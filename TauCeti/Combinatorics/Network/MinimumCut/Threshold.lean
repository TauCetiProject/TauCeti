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

@[simp]
theorem thresholdRelated_def (f : Finset V → K) (k : K) (s t : V) :
    ThresholdRelated f k s t ↔ s = t ∨ k ≤ pairMinimumValue f s t :=
  Iff.rfl

/-- Threshold relatedness is an equivalence relation whenever the minimum cut value is
symmetric. -/
theorem thresholdRelated_equivalence
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) :
    Equivalence (ThresholdRelated f k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact Or.inl rfl
  · rintro s t (rfl | hst)
    · exact Or.inl rfl
    · exact Or.inr <| (hsymm s t) ▸ hst
  · rintro s t u (rfl | hst) (rfl | htu)
    · exact Or.inl rfl
    · exact Or.inr htu
    · exact Or.inr hst
    · by_cases hsu : s = u
      · exact Or.inl hsu
      · exact Or.inr <| (le_min hst htu).trans (min_pairMinimumValue_le f hsu t)

/-- The equivalence relation whose classes are the threshold components. -/
def thresholdSetoid (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) : Setoid V where
  r := ThresholdRelated f k
  iseqv := thresholdRelated_equivalence hsymm k

@[simp]
theorem thresholdSetoid_rel (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) (s t : V) :
    thresholdSetoid f hsymm k s t ↔ s = t ∨ k ≤ pairMinimumValue f s t :=
  Iff.rfl

/-- The abstract type of threshold classes. -/
def ThresholdComponent (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) :=
  Quotient (thresholdSetoid f hsymm k)

/-- The threshold class containing a vertex. -/
def thresholdComponentMk (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s)
    (k : K) (v : V) : ThresholdComponent f hsymm k :=
  Quotient.mk _ v

@[simp]
theorem thresholdComponentMk_eq_iff (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) (s t : V) :
    thresholdComponentMk f hsymm k s = thresholdComponentMk f hsymm k t ↔
      s = t ∨ k ≤ pairMinimumValue f s t :=
  Quotient.eq'

/-- Every threshold component has a vertex representative. -/
theorem thresholdComponentMk_surjective (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) :
    Function.Surjective (thresholdComponentMk f hsymm k) :=
  Quotient.exists_rep

namespace ThresholdComponent

/-- To prove a property of every threshold component, it suffices to prove it on the component
of each vertex. -/
@[elab_as_elim]
protected theorem ind {motive : ThresholdComponent f hsymm k → Prop}
    (h : ∀ v, motive (thresholdComponentMk f hsymm k v))
    (c : ThresholdComponent f hsymm k) : motive c :=
  Quotient.ind h c

end ThresholdComponent

namespace IsFlowEquivalentTree

/-- Threshold relatedness is precisely reachability after deleting the tree edges lighter than
the threshold. -/
theorem thresholdRelated_iff_reachable (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    ThresholdRelated f k s t ↔ (T.deleteEdges {e | w e < k}).Reachable s t :=
  (hT.reachable_deleteEdges_iff k).symm

/-- A flow-equivalent tree makes the minimum cut value symmetric. -/
theorem pairMinimumValue_symmetric (hT : IsFlowEquivalentTree f T w) :
    ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s := by
  intro s t
  by_cases hst : s = t
  · subst t
    rfl
  · have hle : ∀ s t, s ≠ t → pairMinimumValue f s t ≤ pairMinimumValue f t s := by
      intro s t hst
      have hreach :=
        (hT.reachable_deleteEdges_iff (pairMinimumValue f s t)).2 (Or.inr le_rfl)
      exact ((hT.reachable_deleteEdges_iff (pairMinimumValue f s t)).1 hreach.symm).resolve_left
        (Ne.symm hst)
    exact le_antisymm (hle s t hst) (hle t s (Ne.symm hst))

/-- Threshold classes are canonically the connected components of the threshold graph. -/
def thresholdComponentEquiv (hT : IsFlowEquivalentTree f T w) (k : K) :
    ThresholdComponent f hT.pairMinimumValue_symmetric k ≃
      (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  Quotient.congrRight
    (r := thresholdSetoid f hT.pairMinimumValue_symmetric k)
    (r' := (T.deleteEdges {e | w e < k}).reachableSetoid)
    fun s t ↦ hT.thresholdRelated_iff_reachable k s t

@[simp]
theorem thresholdComponentEquiv_apply_mk (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    hT.thresholdComponentEquiv k
        (thresholdComponentMk f hT.pairMinimumValue_symmetric k v) =
      (T.deleteEdges {e | w e < k}).connectedComponentMk v := by
  -- `Quotient.congrRight`, `thresholdComponentMk`, and `connectedComponentMk` all compute on
  -- quotient representatives.
  rfl

@[simp]
theorem thresholdComponentEquiv_symm_apply_mk
    (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    (hT.thresholdComponentEquiv k).symm
        ((T.deleteEdges {e | w e < k}).connectedComponentMk v) =
      thresholdComponentMk f hT.pairMinimumValue_symmetric k v := by
  apply (hT.thresholdComponentEquiv k).injective
  simp

/-- Two vertices determine the same connected component of the threshold graph exactly when they
are equal or their minimum cut value is at least the threshold. -/
theorem connectedComponentMk_threshold_eq_iff
    (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    (T.deleteEdges {e | w e < k}).connectedComponentMk s =
        (T.deleteEdges {e | w e < k}).connectedComponentMk t ↔
      s = t ∨ k ≤ pairMinimumValue f s t := by
  rw [ConnectedComponent.eq, hT.reachable_deleteEdges_iff]

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
    Nat.card (ThresholdComponent f hT.pairMinimumValue_symmetric k) =
      Nat.card (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  Nat.card_congr (hT.thresholdComponentEquiv k)

end IsFlowEquivalentTree

end TauCeti.TerminalCut
