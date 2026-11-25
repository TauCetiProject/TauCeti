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
setoid and gives the corresponding connected-component equality and class-membership formulas.

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
theorem thresholdRelated_iff (f : Finset V → K) (k : K) (s t : V) :
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

namespace IsFlowEquivalentTree

/-- The threshold graph's reachability relation is the minimum-cut threshold setoid. -/
theorem reachableSetoid_deleteEdges_eq_thresholdSetoid
    (hT : IsFlowEquivalentTree f T w) (k : K) :
    (T.deleteEdges {e | w e < k}).reachableSetoid =
      thresholdSetoid f hT.pairMinimumValue_comm k :=
  Setoid.ext fun s t ↦ (hT.reachable_deleteEdges_iff k).trans
    (thresholdSetoid_rel f hT.pairMinimumValue_comm k s t).symm

/-- Two vertices determine the same connected component of the threshold graph exactly when they
are equal or their minimum cut value is at least the threshold. -/
theorem connectedComponentMk_deleteEdges_eq_iff
    (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    (T.deleteEdges {e | w e < k}).connectedComponentMk s =
        (T.deleteEdges {e | w e < k}).connectedComponentMk t ↔
      s = t ∨ k ≤ pairMinimumValue f s t := by
  rw [ConnectedComponent.eq, hT.reachable_deleteEdges_iff]

/-- Membership in the threshold component of `s` is governed by the threshold minimum-cut
relation. -/
theorem mem_supp_connectedComponentMk_deleteEdges_iff
    (hT : IsFlowEquivalentTree f T w) (k : K) (s t : V) :
    t ∈ ((T.deleteEdges {e | w e < k}).connectedComponentMk s).supp ↔
      s = t ∨ k ≤ pairMinimumValue f s t := by
  rw [ConnectedComponent.mem_supp_iff, eq_comm, hT.connectedComponentMk_deleteEdges_eq_iff]

end IsFlowEquivalentTree

end TauCeti.TerminalCut
