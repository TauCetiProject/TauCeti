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
import Mathlib.RingTheory.MvPowerSeries.Inverse
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Module length over multivariate formal power series

For any commutative local ring `R`, the constant-coefficient homomorphism induces an
`R`-algebra isomorphism between the residue field of `MvPowerSeries σ R` and
`IsLocalRing.ResidueField R`. Consequently, the `MvPowerSeries σ R`-module length of any
`MvPowerSeries σ R`-module agrees with its `R`-module length
(`MvPowerSeries.length_restrictScalars`).
-/

public section

namespace MvPowerSeries

/-- For any `MvPowerSeries σ R`-module `M` over a local commutative ring `R`, its `R`-module length
equals its `MvPowerSeries σ R`-module length, since the residue field of `MvPowerSeries σ R` is
`R`-isomorphic to `IsLocalRing.ResidueField R`. -/
theorem length_restrictScalars {σ R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module (MvPowerSeries σ R) M]
    [IsScalarTower R (MvPowerSeries σ R) M] :
    Module.length R M = Module.length (MvPowerSeries σ R) M := by
  have : IsLocalHom (algebraMap R (MvPowerSeries σ R)) :=
    isLocalHom_of_leftInverse MvPowerSeries.constantCoeff fun r ↦ by simp [algebraMap_apply]
  let ev : MvPowerSeries σ R →ₐ[R] IsLocalRing.ResidueField R :=
    { (IsLocalRing.residue R).comp MvPowerSeries.constantCoeff with
      commutes' := fun r ↦ by simp [IsLocalRing.ResidueField.algebraMap_eq, algebraMap_apply] }
  have hev : Function.Surjective ev := fun x ↦ by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨algebraMap R _ r, by simp [ev.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hres : Module.length (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField (MvPowerSeries σ R)) = 1 := by
    rw [← Module.length_eq_of_surjective (S := R) (IsLocalRing.residue_surjective (R := R)),
      (TauCeti.residueFieldAlgEquivOfSurjective hev).toLinearEquiv.length_eq,
      Module.length_eq_of_surjective (S := R) (IsLocalRing.residue_surjective (R := R)),
      Module.length_eq_one]
  rw [IsLocalRing.length_restrictScalars R (MvPowerSeries σ R) M, hres, mul_one]

end MvPowerSeries
