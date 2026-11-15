/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Sphere

/-!
# The first cohomology of the divisor sheaf `𝒪_0` of the Riemann sphere vanishes

The divisor sheaf `𝒪_0` of the zero divisor is the structure sheaf
(`TauCeti.RiemannSurface.divisorSheafZeroIso`), whose degree one Čech cohomology on the Riemann
sphere vanishes by Laurent splitting on a two-disc cover
(`TauCeti.RiemannSurface.isZero_cechCohomology_one_holomorphicStructureSheafModules_sphere`). So
`h¹(𝒪) = 0` on `ℙ¹`.

## Main results

* `TauCeti.RiemannSurface.isZero_divisorCechCohomology_zero_one_sphere` and
  `TauCeti.RiemannSurface.finrank_divisorCechCohomology_zero_one_sphere`: the degree one Čech
  cohomology of `𝒪_0` on `ℙ¹` vanishes, so `h¹(𝒪) = 0`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 13.5 (`H¹(ℙ¹, 𝒪) = 0`).
-/

public noncomputable section

open CategoryTheory Limits TauCeti.Topology

namespace TauCeti.RiemannSurface

/-- **`h¹(𝒪) = 0` on `ℙ¹`.** The degree one Čech cohomology of the divisor sheaf `𝒪_0`, the
structure sheaf, of the Riemann sphere vanishes. -/
theorem isZero_divisorCechCohomology_zero_one_sphere :
    IsZero (divisorCechCohomology (0 : AlgebraicGeometry.WeilDivisor (OnePoint ℂ)) 1) :=
  isZero_cechCohomology_one_holomorphicStructureSheafModules_sphere.of_iso
    ((cechCohomology (TopCat.of (OnePoint ℂ)) (ModuleCat.{0} ℂ) 1).mapIso
      ((sheafToPresheaf _ _).mapIso (divisorSheafZeroIso (OnePoint ℂ))))

/-- The degree one Čech cohomology of the divisor sheaf `𝒪_0` of the Riemann sphere has dimension
zero. -/
theorem finrank_divisorCechCohomology_zero_one_sphere :
    Module.finrank ℂ (divisorCechCohomology (0 : AlgebraicGeometry.WeilDivisor (OnePoint ℂ)) 1) =
      0 :=
  have := ModuleCat.isZero_iff_subsingleton.1 isZero_divisorCechCohomology_zero_one_sphere
  Module.finrank_zero_of_subsingleton

end TauCeti.RiemannSurface
