/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Basic

/-!
# Canonical divisors of the Riemann sphere and `h¹(𝒪)`

Every canonical divisor `K` of `ℙ¹ = OnePoint ℂ`, for example `-2[∞]`
(`TauCeti.RiemannSurface.isCanonicalDivisor_neg_two_infty`), has degree `-2`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_of_sphere`), which is
`2 h¹(𝒪) - 2`. Having negative degree, it has no nonzero global sections, so `h⁰(K) = h¹(𝒪)`,
both being zero.

## Main results

All declarations are in the namespace `TauCeti.RiemannSurface.IsCanonicalDivisor`.

* `isZero_divisorSheaf_globalSections_of_sphere` and
  `finrank_divisorSheaf_globalSections_of_sphere`: every canonical divisor `K` of `ℙ¹` has
  `H⁰(K) = 0`.
* `finrank_divisorSheaf_globalSections_eq_finrank_divisorCechCohomology_zero_one_of_sphere`:
  every canonical divisor `K` of `ℙ¹` has `h⁰(K) = h¹(𝒪)`.
* `degree_eq_two_mul_finrank_divisorCechCohomology_zero_one_sub_two_of_sphere`:
  every canonical divisor `K` of `ℙ¹` has `deg K = 2 h¹(𝒪) - 2`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17.
-/

public section

open CategoryTheory Limits Opposite
open TauCeti.AlgebraicGeometry

namespace TauCeti.RiemannSurface

namespace IsCanonicalDivisor

/-- A canonical divisor of `ℙ¹` has no nonzero global sections, having degree `-2`. -/
theorem isZero_divisorSheaf_globalSections_of_sphere {K : WeilDivisor (OnePoint ℂ)}
    (hK : IsCanonicalDivisor K) : IsZero ((divisorSheaf K).obj.obj (op ⊤)) :=
  isZero_divisorSheaf_globalSections_of_degree_neg (by simp [hK.degree_eq_neg_two_of_sphere])

/-- A canonical divisor `K` of `ℙ¹` has `h⁰(K) = 0`, having degree `-2`. -/
theorem finrank_divisorSheaf_globalSections_of_sphere {K : WeilDivisor (OnePoint ℂ)}
    (hK : IsCanonicalDivisor K) : Module.finrank ℂ ((divisorSheaf K).obj.obj (op ⊤)) = 0 :=
  finrank_divisorSheaf_globalSections_of_degree_neg (by simp [hK.degree_eq_neg_two_of_sphere])

/-- Every canonical divisor `K` of `ℙ¹` has `h⁰(K) = h¹(𝒪)`, both being zero. -/
theorem finrank_divisorSheaf_globalSections_eq_finrank_divisorCechCohomology_zero_one_of_sphere
    {K : WeilDivisor (OnePoint ℂ)} (hK : IsCanonicalDivisor K) :
    Module.finrank ℂ ((divisorSheaf K).obj.obj (op ⊤)) =
      Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor (OnePoint ℂ)) 1) := by
  rw [hK.finrank_divisorSheaf_globalSections_of_sphere,
    finrank_divisorCechCohomology_zero_one_sphere]

/-- Every canonical divisor of `ℙ¹` has degree `2 h¹(𝒪) - 2`, the value `-2` for
`h¹(𝒪) = 0`. -/
theorem degree_eq_two_mul_finrank_divisorCechCohomology_zero_one_sub_two_of_sphere
    {K : WeilDivisor (OnePoint ℂ)} (hK : IsCanonicalDivisor K) :
    WeilDivisor.degree K =
      2 * (Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor (OnePoint ℂ)) 1) : ℤ) - 2 := by
  rw [hK.degree_eq_neg_two_of_sphere, finrank_divisorCechCohomology_zero_one_sphere]
  norm_num

end IsCanonicalDivisor

end TauCeti.RiemannSurface
