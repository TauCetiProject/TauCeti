/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.FubiniStudySphere
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere.Hurewicz

/-!
# The Fubini–Study area on the second homology of the Riemann sphere

The Riemann sphere `OnePoint ℂ` is simply connected, so the integral of the Fubini–Study form
`ω_FS` (`OnePoint.fubiniStudyForm`) over the second homotopy group descends to a homomorphism
`OnePoint.fubiniStudyAreaHom : H₂(OnePoint ℂ; ℤ) →+ ℝ` (`TauCeti.homologySphereIntegralHom`). It
agrees with the integral of `ω_FS` on the Hurewicz class of every sphere, at every base point
(`OnePoint.fubiniStudyAreaHom_hurewiczIntHom`). This is the symplectic area with which capped
Hamiltonian Floer theory on the Riemann sphere builds its period group.

## Main definitions

* `OnePoint.fubiniStudyAreaHom`: the Fubini–Study area on `H₂(OnePoint ℂ; ℤ)`.

## Main results

* `OnePoint.fubiniStudyAreaHom_hurewiczIntHom`: it is the integral of `ω_FS` on Hurewicz classes,
  at every base point.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 11.1 (the symplectic area of spherical classes).
-/

public section

noncomputable section

open AlgebraicTopology HomotopyGroup
open scoped Manifold Topology Topology.Homotopy TauCeti.ComplexManifold

namespace OnePoint

/-- **The Fubini–Study area on `H₂(OnePoint ℂ; ℤ)`**: the integral of the Fubini–Study form over
spheres, transported along the Hurewicz isomorphism. It agrees with the integral of `ω_FS` on the
Hurewicz class of every sphere (`OnePoint.fubiniStudyAreaHom_hurewiczIntHom`). -/
def fubiniStudyAreaHom :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
      (TopCat.of (OnePoint ℂ)) →+ ℝ :=
  TauCeti.homologySphereIntegralHom (fubiniStudyForm.isSmoothForm.of_le (by simp))
    ((TauCeti.SmoothForm.isClosed_def _).1 isSymplectic_fubiniStudyForm.isClosed)

/-- The Fubini–Study area on `H₂(OnePoint ℂ; ℤ)` is the integral of `ω_FS` on Hurewicz classes, at
every base point. -/
@[simp]
theorem fubiniStudyAreaHom_hurewiczIntHom (x : OnePoint ℂ) (a : Additive (π_ 2 (OnePoint ℂ) x)) :
    fubiniStudyAreaHom (hurewiczIntHom _ x 1 a) =
      TauCeti.sphereIntegralHom x (fubiniStudyForm.isSmoothForm.of_le (by simp))
        ((TauCeti.SmoothForm.isClosed_def _).1 isSymplectic_fubiniStudyForm.isClosed) a :=
  TauCeti.homologySphereIntegralHom_hurewiczIntHom _ _ x a

end OnePoint
