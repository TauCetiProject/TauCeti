/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup
import Mathlib.GroupTheory.Nilpotent

/-!
# The Galois group of a finite extension of local fields is solvable

Let `L/K` be a finite extension of nonarchimedean local fields, with automorphism group
`G = L ≃ₐ[K] L` and lower ramification filtration `G_i`. The three steps of the filtration
`1 ⊴ G_1 ⊴ G_0 ⊴ G` have the following quotients:

* `G / G_0` embeds, through the action on the residue field, into the Galois group of the finite
  residue field extension, so it is cyclic;
* the tame quotient `G_0 / G_1` embeds into `𝓀[L]ˣ` through the tame character, so it is cyclic
  (`TauCeti.isCyclic_ramificationGroupGraded_zero`);
* the wild inertia group `G_1` is a `p`-group for the residue characteristic `p`
  (`TauCeti.isPGroup_ramificationGroup`), hence nilpotent.

Consequently `G` is solvable. Solvability is what lets a statement about the cohomology of a
finite local Galois group be proved by induction along a chain of normal subgroups with cyclic
quotients, reducing it to the cyclic case.

## Main results

* `TauCeti.LocalFieldsRamification.isSolvable_algEquiv`: `G` is solvable.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open ValuativeRel TauCeti.IsLocalRing

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- **The Galois group of a finite extension of nonarchimedean local fields is solvable**: its
ramification filtration `1 ⊴ G_1 ⊴ G_0 ⊴ G` has a `p`-group at the bottom and cyclic quotients
above it. -/
instance isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by
  have : Fact (ringChar 𝓀[L]).Prime := ⟨CharP.char_is_prime 𝓀[L] _⟩
  -- Wild inertia `G_1` is a `p`-group, hence nilpotent. It is spelled `G_{0 + 1}`, the subgroup
  -- by which `RamificationGroupGraded _ _ 0` is the quotient of `G_0`.
  have : Group.IsNilpotent (ramificationGroup (L ≃ₐ[K] L) 𝒪[L] (0 + 1)) :=
    (isPGroup_ramificationGroup _ (ringChar 𝓀[L]) (by omega)).isNilpotent
  -- The tame quotient `G_0 / G_1` is cyclic, so inertia `G_0` is solvable.
  have := isCyclic_ramificationGroupGraded_zero L (L ≃ₐ[K] L)
  have hG₀ : Group.IsSolvable (ramificationGroup (L ≃ₐ[K] L) 𝒪[L] 0) :=
    Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion
        (ramificationGroup_antitone (L ≃ₐ[K] L) 𝒪[L] (by omega : (0 : ℤ) ≤ 0 + 1)))
      (QuotientGroup.mk' _) fun x hx ↦
        ⟨⟨x, Subgroup.mem_subgroupOf.mp (by rwa [QuotientGroup.ker_mk'] at hx)⟩, rfl⟩
  rw [← lowerRamificationGroup_def] at hG₀
  -- The quotient `G / G_0` is cyclic.
  have := isCyclic_quotient_lowerRamificationGroup_zero K L
  exact Group.isSolvable_of_subgroup_quotient (lowerRamificationGroup K L 0)

end TauCeti.LocalFieldsRamification
