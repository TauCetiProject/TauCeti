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
  Quotient.eq'.trans (thresholdSetoid_rel f hsymm k s t)

/-- Every threshold component has a vertex representative. -/
theorem thresholdComponentMk_surjective (f : Finset V → K)
    (hsymm : ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s) (k : K) :
    Function.Surjective (thresholdComponentMk f hsymm k) :=
  Quotient.exists_rep

namespace ThresholdComponent

instance instFinite : Finite (ThresholdComponent f hsymm k) :=
  Finite.of_surjective (thresholdComponentMk f hsymm k)
    (thresholdComponentMk_surjective f hsymm k)

instance instInhabited [Inhabited V] : Inhabited (ThresholdComponent f hsymm k) :=
  ⟨thresholdComponentMk f hsymm k default⟩

instance instIsEmpty [IsEmpty V] : IsEmpty (ThresholdComponent f hsymm k) :=
  ⟨fun c ↦ let ⟨v, _⟩ := thresholdComponentMk_surjective f hsymm k c; isEmptyElim v⟩

instance instNonempty [Nonempty V] : Nonempty (ThresholdComponent f hsymm k) :=
  Nonempty.map (thresholdComponentMk f hsymm k) ‹_›

instance instSubsingleton [Subsingleton V] : Subsingleton (ThresholdComponent f hsymm k) :=
  (thresholdComponentMk_surjective f hsymm k).subsingleton

instance instUnique [Unique V] : Unique (ThresholdComponent f hsymm k) :=
  Function.Surjective.unique (thresholdComponentMk f hsymm k)
    (thresholdComponentMk_surjective f hsymm k)

/-- Descend a function on vertices that is constant on threshold-related pairs to threshold
components. -/
protected def lift {B : Sort*} (g : V → B)
    (h : ∀ s t, ThresholdRelated f k s t → g s = g t) : ThresholdComponent f hsymm k → B :=
  Quotient.lift g fun s t hst ↦ h s t ((thresholdSetoid_rel f hsymm k s t).mp hst)

@[simp]
protected theorem lift_mk {B : Sort*} (g : V → B)
    (h : ∀ s t, ThresholdRelated f k s t → g s = g t) (v : V) :
    ThresholdComponent.lift g h (thresholdComponentMk f hsymm k v) = g v :=
  Quotient.lift_mk (s := thresholdSetoid f hsymm k) g
    (fun s t hst ↦ h s t ((thresholdSetoid_rel f hsymm k s t).mp hst)) v

/-- The set of vertices in a threshold component. -/
def supp (c : ThresholdComponent f hsymm k) : Set V :=
  {v | thresholdComponentMk f hsymm k v = c}

@[simp]
theorem mem_supp_iff (c : ThresholdComponent f hsymm k) (v : V) :
    v ∈ c.supp ↔ thresholdComponentMk f hsymm k v = c :=
  Iff.rfl

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
theorem pairMinimumValue_comm (hT : IsFlowEquivalentTree f T w) :
    ∀ s t, pairMinimumValue f s t = pairMinimumValue f t s := by
  intro s t
  by_cases hst : s = t
  · subst t
    rfl
  · have hle : ∀ s t, s ≠ t → pairMinimumValue f s t ≤ pairMinimumValue f t s := by
      intro s t hst
      have hreach := (hT.thresholdRelated_iff_reachable (pairMinimumValue f s t) s t).mp
        ((thresholdRelated_def f (pairMinimumValue f s t) s t).mpr (Or.inr le_rfl))
      exact
        ((thresholdRelated_def f (pairMinimumValue f s t) t s).mp
          ((hT.thresholdRelated_iff_reachable
            (pairMinimumValue f s t) t s).mpr hreach.symm)).resolve_left (Ne.symm hst)
    exact le_antisymm (hle s t hst) (hle t s (Ne.symm hst))

/-- Threshold classes are canonically the connected components of the threshold graph. -/
def thresholdComponentEquiv (hT : IsFlowEquivalentTree f T w) (k : K) :
    ThresholdComponent f hT.pairMinimumValue_comm k ≃
      (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  Quotient.congrRight
    (r := thresholdSetoid f hT.pairMinimumValue_comm k)
    (r' := (T.deleteEdges {e | w e < k}).reachableSetoid)
    fun s t ↦ (thresholdSetoid_rel f hT.pairMinimumValue_comm k s t).trans
      (hT.reachable_deleteEdges_iff k).symm

@[simp]
theorem thresholdComponentEquiv_apply_mk (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    hT.thresholdComponentEquiv k
        (thresholdComponentMk f hT.pairMinimumValue_comm k v) =
      (T.deleteEdges {e | w e < k}).connectedComponentMk v := by
  -- `Quotient.congrRight`, `thresholdComponentMk`, and `connectedComponentMk` all compute on
  -- quotient representatives.
  rfl

@[simp]
theorem thresholdComponentEquiv_symm_apply_mk
    (hT : IsFlowEquivalentTree f T w) (k : K) (v : V) :
    (hT.thresholdComponentEquiv k).symm
        ((T.deleteEdges {e | w e < k}).connectedComponentMk v) =
      thresholdComponentMk f hT.pairMinimumValue_comm k v := by
  apply (hT.thresholdComponentEquiv k).injective
  simp

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

/-- The canonical equivalence preserves the vertex support of each threshold component. -/
theorem thresholdComponentEquiv_supp (hT : IsFlowEquivalentTree f T w) (k : K)
    (c : ThresholdComponent f hT.pairMinimumValue_comm k) :
    (hT.thresholdComponentEquiv k c).supp = c.supp := by
  induction c using ThresholdComponent.ind with
  | _ s =>
    ext v
    simp only [ConnectedComponent.mem_supp_iff, ThresholdComponent.mem_supp_iff,
      thresholdComponentEquiv_apply_mk]
    constructor
    · exact fun h ↦ (hT.thresholdComponentEquiv k).injective (by simpa using h)
    · exact fun h ↦ by simpa using congrArg (hT.thresholdComponentEquiv k) h

/-- The abstract threshold quotient and the graph's connected-component type have the same
cardinality. -/
theorem natCard_thresholdComponent_eq (hT : IsFlowEquivalentTree f T w) (k : K) :
    Nat.card (ThresholdComponent f hT.pairMinimumValue_comm k) =
      Nat.card (T.deleteEdges {e | w e < k}).ConnectedComponent :=
  Nat.card_congr (hT.thresholdComponentEquiv k)

end IsFlowEquivalentTree

end TauCeti.TerminalCut
