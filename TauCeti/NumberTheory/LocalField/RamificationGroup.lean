/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Lower ramification groups of a local field extension

For a finite Galois extension `L/K` of nonarchimedean local fields, the canonical lower
ramification group consists of automorphisms acting trivially on the integer ring modulo
the `(i + 1)`-st power of its maximal ideal. The integer index is total: at `i ≤ -1` the
group is the full Galois group.

This is the local field specialization of `TauCeti.IsLocalRing.ramificationGroup`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The lower-numbering ramification group of a finite extension of local fields. -/
def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) :=
  TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i

/-- The local-field filtration is the ramification filtration of its integer ring. -/
theorem lowerRamificationGroup_def (i : ℤ) :
    lowerRamificationGroup K L i =
      TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i :=
  (rfl)

/-- At nonnegative indices, the canonical lower group is the maximal-ideal ramification group. -/
theorem lowerRamificationGroup_natCast (i : ℕ) :
    lowerRamificationGroup K L i =
      (IsLocalRing.maximalIdeal 𝒪[L]).ramificationGroup (L ≃ₐ[K] L) i := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_natCast]

end TauCeti.LocalFieldsRamification
