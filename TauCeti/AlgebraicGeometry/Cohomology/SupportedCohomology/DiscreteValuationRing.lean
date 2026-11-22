/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.DiscreteValuationRing
public import TauCeti.AlgebraicGeometry.Cohomology.SupportedCohomology.Basic

/-!
# Supported sheaf cohomology of a discrete valuation ring

For a discrete valuation ring `(R, 𝔪)` with fraction ring `K`, transferring the algebraic local
cohomology computation (`TauCeti.Algebra.Homology.LocalCohomology.DiscreteValuationRing`) across
`TauCeti.AlgebraicGeometry.supportedModuleHTopTildeLinearEquivLocalCohomology` gives the supported
cohomology of the structure sheaf at the closed point `V(𝔪)` of `Spec R`:
`H⁰_{V(𝔪)} = 0`, `H¹_{V(𝔪)} ≃ₗ[R] K ⧸ R`, and `H^{n+2}_{V(𝔪)} = 0`.

## Main definitions

* `TauCeti.AlgebraicGeometry.supportedModuleHDvrDegreeOneLinearEquiv`: the `R`-linear equivalence
  `H¹_{V(𝔪)}(Spec R, 𝒪_{Spec R}) ≃ₗ[R] K ⧸ R`.

## Main results

* `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_dvr_zero` and
  `TauCeti.AlgebraicGeometry.subsingleton_supportedModuleH_dvr_add_two`: vanishing of
  `H⁰_{V(𝔪)}(Spec R, 𝒪_{Spec R})` and `H^{n+2}_{V(𝔪)}(Spec R, 𝒪_{Spec R})`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Exercise III.3.3.
* A. Grothendieck, *Local Cohomology* (notes by R. Hartshorne), Lecture Notes in Mathematics 41,
  Springer, 1967, Proposition 2.8.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

section DiscreteValuationRing

variable (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- Over a discrete valuation ring `(R, 𝔪)`, `H⁰_{V(𝔪)}(Spec R, 𝒪_{Spec R}) = 0`. -/
theorem subsingleton_supportedModuleH_dvr_zero :
    Subsingleton ((modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ 0) := by
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_dvr_zero R)
  exact (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) 0).subsingleton

/-- Over a discrete valuation ring `(R, 𝔪)` with fraction field `K`,
`H¹_{V(𝔪)}(Spec R, 𝒪_{Spec R}) ≃ₗ[R] K ⧸ R`. -/
def supportedModuleHDvrDegreeOneLinearEquiv :
    (modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
        (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ 1 ≃ₗ[R]
      K ⧸ LinearMap.range (Algebra.linearMap R K) :=
  (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) 1).trans (localCohomology.dvrDegreeOneLinearEquiv R K)

/-- Over a discrete valuation ring `(R, 𝔪)`, `H^{n+2}_{V(𝔪)}(Spec R, 𝒪_{Spec R}) = 0`. -/
theorem subsingleton_supportedModuleH_dvr_add_two (n : ℕ) :
    Subsingleton ((modulesSpecToSheaf.obj (tilde (.of R R))).supportedModuleH
      (Spec.zeroLocusClosed (R := R) (IsLocalRing.maximalIdeal R : Set R)) ⊤ (n + 2)) :=
  have := ModuleCat.subsingleton_of_isZero (localCohomology.isZero_dvr_add_two R n)
  (supportedModuleHTopTildeLinearEquivLocalCohomology (R := R)
    (IsLocalRing.maximalIdeal R) (.of R R) (n + 2)).subsingleton

end DiscreteValuationRing

end TauCeti.AlgebraicGeometry
