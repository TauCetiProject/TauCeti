/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.NormalSubgroup.ChiefSeries
public import TauCeti.GroupTheory.CompositionSeries.Basic

/-!
# Refining normal-inclusion chains to group composition series

A chain of normal inclusions refines to a series of composition steps when the subgroup lattice
of its last term satisfies both chain conditions. Concatenating composition series for the normal
intervals preserves every term of the original chain. Chief series are a special case.

The concatenation argument follows Mathlib's `LTSeries.exists_relSeries_covBy`, replacing
order covers with composition steps in the relevant subgroup intervals.

## Main results

* `TauCeti.exists_relSeries_isCompositionStep_refinement`: refinement of a normal-inclusion chain.
* `TauCeti.ChiefSeries.exists_relSeries_isCompositionStep_refinement`: refinement of a chief series.
* `TauCeti.ChiefSeries.exists_groupCompositionSeries_refinement`: refinement from `⊥` to `⊤` when
  the ambient group's subgroup lattice has no infinite ascending or descending chain.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A chain of normal inclusions refines to composition steps, preserving its endpoints and all
its terms, if the subgroup lattice of its last term has no infinite ascending or descending
chain. -/
theorem exists_relSeries_isCompositionStep_refinement
    (s : RelSeries {p : Subgroup G × Subgroup G | p.1 ≤ p.2 ∧ (p.1.subgroupOf p.2).Normal})
    [WellFoundedLT (Subgroup s.last)] [WellFoundedGT (Subgroup s.last)] :
    ∃ t : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
      t.head = s.head ∧ t.last = s.last ∧ ∀ H ∈ s, H ∈ t := by
  revert ‹WellFoundedLT (Subgroup s.last)› ‹WellFoundedGT (Subgroup s.last)›
  induction s using RelSeries.inductionOn' with
  | singleton A =>
    intro _ _
    refine ⟨RelSeries.singleton _ A, by simp only [RelSeries.head_singleton],
      by simp only [RelSeries.last_singleton], ?_⟩
    rintro H ⟨i, rfl⟩
    have hi : i = 0 := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
        (by simpa only [RelSeries.singleton_length] using i.isLt))
    subst i
    refine ⟨0, ?_⟩
    simp only [RelSeries.apply_zero, RelSeries.head_singleton]
  | snoc s B hstep ih =>
    intro hlt hgt
    have : WellFoundedLT (Subgroup B) := (RelSeries.last_snoc s B hstep) ▸ hlt
    have : WellFoundedGT (Subgroup B) := (RelSeries.last_snoc s B hstep) ▸ hgt
    let e : Subgroup s.last ↪o Subgroup B := OrderEmbedding.ofMapLEIff
      (Subgroup.map (Subgroup.inclusion hstep.1))
      (fun _ _ ↦ Subgroup.map_le_map_iff_of_injective (Subgroup.inclusion_injective _))
    obtain ⟨t, htHead, htLast, htMem⟩ := @ih e.wellFoundedLT e.wellFoundedGT
    obtain ⟨u, huHead, huLast⟩ := exists_relSeries_isCompositionStep_between
      (A := s.last) (B := B) hstep.1 hstep.2
    have hconnect : t.last = u.head := htLast.trans huHead.symm
    have hleft : ∀ H ∈ t, H ∈ t.smash u hconnect := by
      rintro H ⟨j, hj⟩
      exact ⟨j.castLE (by simp), (RelSeries.smash_castLE hconnect j).trans hj⟩
    refine ⟨t.smash u hconnect, by simpa using htHead, by simpa using huLast, ?_⟩
    intro H hH
    rcases RelSeries.mem_snoc.mp hH with hH | rfl
    · exact hleft H (htMem H hH)
    · rw [← huLast, ← RelSeries.last_smash hconnect]
      exact RelSeries.last_mem _

/-- A chief series refines to composition steps with the same endpoints and every original term
if the subgroup lattice of its last term has no infinite ascending or descending chain. -/
theorem ChiefSeries.exists_relSeries_isCompositionStep_refinement (s : ChiefSeries G)
    [WellFoundedLT (Subgroup (s.last : Subgroup G))]
    [WellFoundedGT (Subgroup (s.last : Subgroup G))] :
    ∃ t : RelSeries {p : Subgroup G × Subgroup G | p.1.IsCompositionStep p.2},
      t.head = (s.head : Subgroup G) ∧ t.last = (s.last : Subgroup G) ∧
      ∀ i, ∃ j, t j = (s i : Subgroup G) := by
  let c : RelSeries {p : Subgroup G × Subgroup G |
      p.1 ≤ p.2 ∧ (p.1.subgroupOf p.2).Normal} :=
    s.map ⟨fun N ↦ (N : Subgroup G), fun {_ _} h ↦ ⟨h.le, inferInstance⟩⟩
  have hlast : c.last = (s.last : Subgroup G) := RelSeries.last_map ..
  have : WellFoundedLT (Subgroup c.last) := by rw [hlast]; infer_instance
  have : WellFoundedGT (Subgroup c.last) := by rw [hlast]; infer_instance
  obtain ⟨t, htHead, htLast, htMem⟩ := TauCeti.exists_relSeries_isCompositionStep_refinement c
  refine ⟨t, ?_, htLast.trans hlast, fun i ↦ htMem _ ⟨i, ?_⟩⟩
  · simpa only [c, RelSeries.head_map, RelHom.coeFn_mk] using htHead
  · exact RelSeries.map_apply ..

/-- A chief series from the trivial subgroup to the whole group refines to a group composition
series containing every chief term, if the subgroup lattice of the group satisfies both chain
conditions. -/
theorem ChiefSeries.exists_groupCompositionSeries_refinement
    [WellFoundedLT (Subgroup G)] [WellFoundedGT (Subgroup G)]
    (s : ChiefSeries G) (hhead : s.head = ⊥) (hlast : s.last = ⊤) :
    ∃ t : GroupCompositionSeries G, ∀ i, ∃ j, t j = (s i : Subgroup G) := by
  let e : Subgroup (s.last : Subgroup G) ↪o Subgroup G := OrderEmbedding.ofMapLEIff
    (Subgroup.map (s.last : Subgroup G).subtype)
    (fun _ _ ↦ Subgroup.map_le_map_iff_of_injective (s.last : Subgroup G).subtype_injective)
  have := e.wellFoundedLT
  have := e.wellFoundedGT
  obtain ⟨t, htHead, htLast, htMem⟩ := s.exists_relSeries_isCompositionStep_refinement
  refine ⟨⟨t, ?_, ?_⟩, htMem⟩
  · simpa only [hhead, CompleteSublattice.coe_bot] using htHead
  · simpa only [hlast, CompleteSublattice.coe_top] using htLast

end TauCeti
