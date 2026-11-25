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

A chief series whose last term is finite refines to a series of composition steps containing
all its terms. Each normal interval between consecutive chief terms has a composition series,
and concatenating these interval series gives the refinement. For a chief series from the
trivial subgroup to the whole finite group, this yields a group composition series.

## Main results

* `TauCeti.ChiefSeries.exists_relSeries_isCompositionStep_refinement`: a chief series with a
  finite last term refines to a series of composition steps with the same endpoints and
  containing every chief term.
* `TauCeti.ChiefSeries.exists_groupCompositionSeries_refinement`: a chief series with endpoints
  `⊥` and `⊤` refines to a group composition series containing every chief term.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A chief series with a finite last term refines to a series of composition steps with the
same endpoints and containing every term of the chief series. -/
theorem ChiefSeries.exists_relSeries_isCompositionStep_refinement (s : ChiefSeries G)
    [Finite (s.last : Subgroup G)] :
    ∃ t : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
      t.head = (s.head : Subgroup G) ∧ t.last = (s.last : Subgroup G) ∧
      ∀ i, ∃ j, t j = (s i : Subgroup G) := by
  revert ‹Finite (s.last : Subgroup G)›
  induction s using RelSeries.inductionOn' with
  | singleton A =>
    intro _
    exact ⟨RelSeries.singleton _ (A : Subgroup G), rfl, rfl, fun _ ↦ ⟨0, rfl⟩⟩
  | snoc s B hstep ih =>
    intro hfinite
    let : Finite (B : Subgroup G) := by
      simpa only [RelSeries.last_snoc] using hfinite
    let : Finite (s.last : Subgroup G) :=
      Finite.of_injective (Subgroup.inclusion hstep.le)
        (Subgroup.inclusion_injective hstep.le)
    obtain ⟨t, htHead, htLast, htMem⟩ := ih
    obtain ⟨u, huHead, huLast⟩ := exists_relSeries_isCompositionStep_between
      (A := (s.last : Subgroup G)) (B := (B : Subgroup G)) hstep.le inferInstance
    have hconnect : t.last = u.head := htLast.trans huHead.symm
    refine ⟨t.smash u hconnect, ?_, ?_, ?_⟩
    · simpa using htHead
    · simpa using huLast
    · intro i
      refine Fin.lastCases ?_ (fun k ↦ ?_) i
      · refine ⟨Fin.last _, ?_⟩
        simp only [RelSeries.apply_last, RelSeries.last_smash, RelSeries.last_snoc, huLast]
      · obtain ⟨j, hj⟩ := htMem k
        refine ⟨j.castLE (by simp), ?_⟩
        rw [RelSeries.smash_castLE, RelSeries.snoc_castSucc s B hstep k, hj]

/-- A chief series from the trivial subgroup to the whole finite group refines to a group
composition series containing every term of the chief series. -/
theorem ChiefSeries.exists_groupCompositionSeries_refinement [Finite G]
    (s : ChiefSeries G) (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    ∃ t : GroupCompositionSeries G, ∀ i, ∃ j, t j = (s i : Subgroup G) := by
  obtain ⟨t, htHead, htLast, htMem⟩ := s.exists_relSeries_isCompositionStep_refinement
  refine ⟨⟨t, ?_, ?_⟩, htMem⟩
  · simpa only [hhead, CompleteSublattice.coe_bot] using htHead
  · simpa only [hlast, CompleteSublattice.coe_top] using htLast

end TauCeti
