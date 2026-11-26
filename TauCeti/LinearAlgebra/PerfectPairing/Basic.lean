/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Unit and sign scaling of perfect pairings

Scaling a perfect bilinear pairing `p : M →ₗ[R] N →ₗ[R] R` over a commutative semiring `R` by a
unit (`LinearMap.IsPerfPair.smul_of_isUnit`, `LinearMap.IsPerfPair.units_smul`) preserves
`LinearMap.IsPerfPair`, and over a commutative ring `R` so do negation (`LinearMap.IsPerfPair.neg`)
and sign scaling by `ℤˣ` (`LinearMap.IsPerfPair.intUnits_smul`).
-/

public section

namespace LinearMap

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Scaling a perfect pairing by a unit of the base commutative semiring preserves perfectness. -/
theorem IsPerfPair.smul_of_isUnit {c : R} (hc : IsUnit c) (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (c • p).IsPerfPair := by
  obtain ⟨u, rfl⟩ := hc
  convert (inferInstance : (p.compl₁₂ (LinearEquiv.smulOfUnit u).toLinearMap
    (LinearEquiv.refl R N).toLinearMap).IsPerfPair)
  ext x y; simp [LinearEquiv.smulOfUnit, Units.smul_def]

/-- Scaling a perfect pairing by `u : Rˣ` preserves perfectness. -/
instance IsPerfPair.units_smul (u : Rˣ) (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (u • p).IsPerfPair :=
  Units.smul_def u p ▸ IsPerfPair.smul_of_isUnit u.isUnit p

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Negating a perfect pairing preserves perfectness. -/
instance IsPerfPair.neg (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] : (-p).IsPerfPair :=
  neg_one_smul R p ▸ IsPerfPair.smul_of_isUnit isUnit_one.neg p

/-- Scaling a perfect pairing by a sign unit `u : ℤˣ` preserves perfectness. -/
instance IsPerfPair.intUnits_smul (u : ℤˣ) (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (u • p).IsPerfPair := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa only [one_smul] using ‹p.IsPerfPair›
  · simpa only [Units.neg_smul, one_smul] using inferInstanceAs (-p).IsPerfPair

end CommRing

end LinearMap
