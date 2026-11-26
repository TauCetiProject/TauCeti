/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# The Galois group of a finite extension of local fields is solvable

Let `L/K` be a finite extension of nonarchimedean local fields, with automorphism group
`G = L ≃ₐ[K] L` and lower ramification filtration `G_i`. The inertia subgroup `G_0` is solvable
because all of its successive ramification quotients are commutative and the filtration reaches `⊥`
in finitely many steps (`TauCeti.IsLocalRing.isSolvable_ramificationGroup_zero`), while `G / G_0`
embeds into the Galois group of the finite residue field extension and is therefore cyclic
(`TauCeti.LocalFieldsRamification.isCyclic_quotient_lowerRamificationGroup_zero`).

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
inertia subgroup `G_0` is solvable and the quotient `G / G_0` is cyclic. -/
instance isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by
  have : Group.IsSolvable (lowerRamificationGroup K L 0) := by
    rw [lowerRamificationGroup_def]
    exact IsLocalRing.isSolvable_ramificationGroup_zero (L ≃ₐ[K] L) 𝒪[L]
      (FixedPoints.subalgebra ℤ 𝒪[L] (L ≃ₐ[K] L))
  have := isCyclic_quotient_lowerRamificationGroup_zero K L
  exact Group.isSolvable_of_subgroup_quotient (lowerRamificationGroup K L 0)

end TauCeti.LocalFieldsRamification
