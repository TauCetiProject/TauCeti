/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.NormalSubgroup.ChiefSeries
public import TauCeti.GroupTheory.CompositionSeries.Basic

/-!
# Refining chief series to group composition series

Every chief series from the trivial subgroup to the whole finite group refines to a group
composition series containing all its terms. Each normal interval between consecutive chief
terms has a composition series, and concatenating these interval series gives the refinement.

## Main results

* `TauCeti.ChiefSeries.exists_groupCompositionSeries_refinement`: a chief series with endpoints
  `⊥` and `⊤` refines to a group composition series containing every chief term.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A chief series from the trivial subgroup to the whole finite group refines to a group
composition series containing every term of the chief series. -/
theorem ChiefSeries.exists_groupCompositionSeries_refinement [Finite G]
    (s : ChiefSeries G) (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    ∃ t : GroupCompositionSeries G, ∀ i, ∃ j, t j = (s i : Subgroup G) := by
  have hRefine (s : ChiefSeries G) :
      ∃ t : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
        t.head = (s.head : Subgroup G) ∧ t.last = (s.last : Subgroup G) ∧
        ∀ i, ∃ j, t j = (s i : Subgroup G) := by
    induction s using RelSeries.inductionOn' with
    | singleton A =>
      exact ⟨RelSeries.singleton _ (A : Subgroup G), rfl, rfl, fun _ ↦ ⟨0, rfl⟩⟩
    | snoc s B hstep ih =>
      obtain ⟨t, htHead, htLast, htMem⟩ := ih
      obtain ⟨u, huHead, huLast⟩ := exists_groupCompositionSeries_between
        (A := (s.last : Subgroup G)) (B := (B : Subgroup G)) hstep.le inferInstance
      have hconnect : t.last = u.head := htLast.trans huHead.symm
      refine ⟨t.smash u hconnect, ?_, ?_, ?_⟩
      · simpa using htHead
      · simpa using huLast
      · intro i
        refine Fin.lastCases ?_ (fun k ↦ ?_) i
        · refine ⟨Fin.last _, ?_⟩
          exact (RelSeries.last_smash hconnect).trans (huLast.trans
            (congrArg (fun N : NormalSubgroup G ↦ (N : Subgroup G))
              (RelSeries.last_snoc s B hstep)).symm)
        · obtain ⟨j, hj⟩ := htMem k
          refine ⟨j.castLE (by simp), ?_⟩
          rw [RelSeries.smash_castLE, hj]
          exact congrArg (fun N : NormalSubgroup G ↦ (N : Subgroup G))
            (RelSeries.snoc_castSucc s B hstep k).symm
  obtain ⟨t, htHead, htLast, htMem⟩ := hRefine s
  refine ⟨⟨t, ?_, ?_⟩, htMem⟩
  · exact htHead.trans (congrArg (fun N : NormalSubgroup G ↦ (N : Subgroup G)) hhead)
  · exact htLast.trans (congrArg (fun N : NormalSubgroup G ↦ (N : Subgroup G)) hlast)

end TauCeti
