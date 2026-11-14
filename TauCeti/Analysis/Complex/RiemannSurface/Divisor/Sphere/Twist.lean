/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Basic
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Map

/-!
# Divisor cohomology on the Riemann sphere

For a divisor `D` on the Riemann sphere `ℙ¹ = OnePoint ℂ`, specializing the point-twist
Euler-characteristic calculation on a compact connected curve to `h¹(𝒪) = 0` shows that
`H¹(𝒪(D))` is finite-dimensional with `h⁰(𝒪(D)) - h¹(𝒪(D)) = deg D + 1`. Since
`h⁰(𝒪(D)) = 0` for `deg D < 0` and `h¹` does not increase with `D`, we obtain

`h⁰(𝒪(D)) = max(deg D + 1, 0)` and `h¹(𝒪(D)) = max(-deg D - 1, 0)`.

In particular a divisor of degree `-1`, such as `-[x]`, has `(h⁰, h¹) = (0, 0)`, and a divisor of
degree `-2` has `(h⁰, h¹) = (0, 1)`. Neither the finiteness of `H¹(𝒪)` nor Serre duality is
asserted for curves of higher genus.

## Main results

All declarations are in the namespace `TauCeti.RiemannSurface`.

* `finiteDimensional_divisorCechCohomology_one_sphere`: `H¹(𝒪(D))` is
  finite-dimensional.
* `finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one_sphere`:
  `h⁰(𝒪(D)) - h¹(𝒪(D)) = deg D + 1`.
* `finrank_divisorCechCohomology_one_sphere_of_neg_one_le_degree` and
  `isZero_divisorCechCohomology_one_sphere_of_neg_one_le_degree`:
  `h¹(𝒪(D)) = 0` for `deg D ≥ -1`.
* `finrank_divisorSheaf_globalSections_sphere` and
  `finrank_divisorCechCohomology_one_sphere`: the closed dimension
  formulas.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-17.
-/

public noncomputable section

open CategoryTheory Limits OnePoint Opposite
open TauCeti.AlgebraicGeometry

namespace TauCeti.RiemannSurface

/-- Every divisor sheaf on `ℙ¹` has finite-dimensional `H¹`, since `H¹(𝒪) = 0`. -/
instance finiteDimensional_divisorCechCohomology_one_sphere (D : WeilDivisor (OnePoint ℂ)) :
    FiniteDimensional ℂ (divisorCechCohomology D 1) :=
  have := ModuleCat.isZero_iff_subsingleton.1 isZero_divisorCechCohomology_zero_one_sphere
  (finiteDimensional_divisorCechCohomology_one_iff D 0).2 inferInstance

/-- **Riemann–Roch on `ℙ¹`.** `h⁰(𝒪(D)) - h¹(𝒪(D)) = deg D + 1`. -/
theorem finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one_sphere
    (D : WeilDivisor (OnePoint ℂ)) :
    (Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) : ℤ) -
      Module.finrank ℂ (divisorCechCohomology D 1) = WeilDivisor.degree D + 1 := by
  rw [finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one,
    finrank_divisorCechCohomology_zero_one_sphere]
  simp

/-- `h¹(𝒪(D)) = 0` on `ℙ¹` when `deg D ≥ -1`. -/
theorem finrank_divisorCechCohomology_one_sphere_of_neg_one_le_degree
    {D : WeilDivisor (OnePoint ℂ)} (hD : -1 ≤ WeilDivisor.degree D) :
    Module.finrank ℂ (divisorCechCohomology D 1) = 0 := by
  obtain ⟨E, hle, hE⟩ : ∃ E ≤ D, WeilDivisor.degree E = -1 :=
    ⟨D - (WeilDivisor.degree D + 1) • WeilDivisor.ofPoint ∞,
      sub_le_self _ (zsmul_nonneg (WeilDivisor.ofPoint_nonneg _) (by omega)), by simp⟩
  have h := finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one_sphere E
  rw [finrank_divisorSheaf_globalSections_of_degree_neg (by omega), hE] at h
  have := finrank_divisorCechCohomology_one_le_of_le hle
  omega

/-- `H¹(𝒪(D))` vanishes on `ℙ¹` when `deg D ≥ -1`. -/
theorem isZero_divisorCechCohomology_one_sphere_of_neg_one_le_degree
    {D : WeilDivisor (OnePoint ℂ)} (hD : -1 ≤ WeilDivisor.degree D) :
    IsZero (divisorCechCohomology D 1) :=
  ModuleCat.isZero_iff_subsingleton.2 <| Module.finrank_zero_iff.1 <|
    finrank_divisorCechCohomology_one_sphere_of_neg_one_le_degree hD

/-- **The dimension of `H⁰` of a divisor sheaf on `ℙ¹`.** `h⁰(𝒪(D)) = max(deg D + 1, 0)`. -/
@[simp]
theorem finrank_divisorSheaf_globalSections_sphere (D : WeilDivisor (OnePoint ℂ)) :
    Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) = (WeilDivisor.degree D + 1).toNat := by
  have h := finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one_sphere D
  rcases le_or_gt 0 (WeilDivisor.degree D) with hD | hD
  · rw [finrank_divisorCechCohomology_one_sphere_of_neg_one_le_degree (by omega)] at h
    omega
  · rw [finrank_divisorSheaf_globalSections_of_degree_neg hD]
    omega

/-- **The dimension of `H¹` of a divisor sheaf on `ℙ¹`.** `h¹(𝒪(D)) = max(-deg D - 1, 0)`. -/
@[simp]
theorem finrank_divisorCechCohomology_one_sphere (D : WeilDivisor (OnePoint ℂ)) :
    Module.finrank ℂ (divisorCechCohomology D 1) = (-WeilDivisor.degree D - 1).toNat := by
  have h := finrank_divisorSheaf_globalSections_sub_finrank_divisorCechCohomology_one_sphere D
  rw [finrank_divisorSheaf_globalSections_sphere] at h
  omega

end TauCeti.RiemannSurface
