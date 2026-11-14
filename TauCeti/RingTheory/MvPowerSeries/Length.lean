/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# Module length over formal power series rings

Over a local commutative ring `R`, the canonical inclusion `R → MvPowerSeries σ R` is a local
homomorphism inducing an isomorphism on residue fields (`MvPowerSeries.residue_C_constantCoeff`).
By `IsLocalRing.length_restrictScalars`, any `MvPowerSeries σ R`-module `M` therefore has the same
length over `R` as over `MvPowerSeries σ R` (`MvPowerSeries.length_restrictScalars`).

## Main results

* `MvPowerSeries.length_restrictScalars`: over a local commutative ring `R`,
  `Module.length R M = Module.length (MvPowerSeries σ R) M`.
-/

public section

namespace MvPowerSeries

/-- Over a local commutative ring `R`, the `R`-module length of any `(MvPowerSeries σ R)`-module `M`
agrees with its `(MvPowerSeries σ R)`-module length, because `R → MvPowerSeries σ R` induces an
isomorphism of residue fields. -/
theorem length_restrictScalars {σ R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
    [IsScalarTower R (MvPowerSeries σ R) M] :
    Module.length R M = Module.length (MvPowerSeries σ R) M := by
  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (MvPowerSeries σ R))) := fun y ↦ by
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨IsLocalRing.residue R (constantCoeff f), ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue, ← c_eq_algebraMap, residue_C_constantCoeff]
  have hres : Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (MvPowerSeries σ R)) = 1 := by
    rw [Module.length_eq_of_surjective hsurj, Module.length_eq_one]
  rw [IsLocalRing.length_restrictScalars R (MvPowerSeries σ R) M, hres, mul_one]

end MvPowerSeries
