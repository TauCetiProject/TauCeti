/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Paracompact

/-!
# Paracompactness of regular Lindelöf spaces

Every regular Lindelöf space is paracompact. No separation axiom beyond regularity is needed.
This applies to weak colimits once normality, the T1 property and Lindelöfness have been proved,
without requiring local compactness of the colimit.

The refinement uses a countable cover by open sets whose closures lie in members of the given
cover. Remove the closures of all preceding small sets from each corresponding cover member.
The resulting open sets cover, and near a point in the m-th small set only the first m+1 sets
can occur.

## References

* J. Munkres, *Topology*, second edition, Section 41, for paracompactness and the
  regular Lindelöf theorem.
-/

public section

open Set Topology

namespace TauCeti

/-- Every regular Lindelöf space is paracompact, without a Hausdorff assumption. -/
theorem paracompactSpace_of_regularSpace_lindelofSpace (X : Type*) [TopologicalSpace X]
    [RegularSpace X] [LindelofSpace X] : ParacompactSpace X := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h => exact inferInstance
  | inr h =>
    refine ⟨fun ι U hU hcover ↦ ?_⟩
    choose i hi using iUnion_eq_univ_iff.mp hcover
    choose V hV hsmall using fun x : X ↦
      (hasBasis_opens_closure x).mem_iff.mp ((hU (i x)).mem_nhds (hi x))
    obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover V (fun x ↦ (hV x).2)
      (fun x _ ↦ mem_iUnion.mpr ⟨x, (hV x).1⟩)
    let W (n : ℕ) := U (i (a n)) \ ⋃ k ∈ Finset.range n, closure (V (a k))
    have hW (n : ℕ) : IsOpen (W n) :=
      (hU _).sdiff (isClosed_biUnion_finset fun _ _ ↦ isClosed_closure)
    -- Use the first small closure containing a point to prove coverage.
    have hWcover : ⋃ n, W n = univ := by
      apply iUnion_eq_univ_iff.mpr
      intro x
      have hex : ∃ n, x ∈ closure (V (a n)) := by
        obtain ⟨n, hn⟩ := mem_iUnion.mp (ha (mem_univ x))
        exact ⟨n, subset_closure hn⟩
      refine ⟨Nat.find hex, hsmall _ (Nat.find_spec hex), ?_⟩
      simp only [mem_iUnion, Finset.mem_range, not_exists]
      exact fun k hk ↦ Nat.find_min hex hk
    -- Inside a small set, all later refinement members have already removed that set.
    have hWfinite : LocallyFinite W := by
      intro x
      obtain ⟨m, hm⟩ := mem_iUnion.mp (ha (mem_univ x))
      refine ⟨V (a m), (hV _).2.mem_nhds hm, (finite_le_nat m).subset ?_⟩
      rintro n ⟨y, hyW, hyV⟩
      by_contra hn
      exact hyW.2 (mem_iUnion₂.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_of_not_ge hn),
        subset_closure hyV⟩)
    refine ⟨ULift ℕ, fun n ↦ W n.down, fun n ↦ hW n.down, ?_,
      hWfinite.comp_injective ULift.down_injective, fun n ↦ ⟨i (a n.down), sdiff_subset⟩⟩
    exact iUnion_eq_univ_iff.mpr fun x ↦
      let ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hWcover x
      ⟨⟨n⟩, hn⟩

end TauCeti
