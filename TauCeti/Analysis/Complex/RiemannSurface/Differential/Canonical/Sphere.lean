/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere.Twist

/-!
# Canonical divisors of the Riemann sphere and `h¹(𝒪)`

The canonical divisor `-2[∞]` of `ℙ¹ = OnePoint ℂ`
(`TauCeti.RiemannSurface.isCanonicalDivisor_neg_two_infty`) is the point twist `𝒪(-2)`, so
`h⁰(K) = h¹(𝒪)`, both being zero. Every canonical divisor of `ℙ¹` has degree `-2`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_of_sphere`), which is
`2 h¹(𝒪) - 2`.

## Main results

All declarations are in the namespace `TauCeti.RiemannSurface`.

* `finrank_divisorSheaf_neg_two_infty_globalSections_eq_finrank_divisorCechCohomology_zero_one`:
  `h⁰(-2[∞]) = h¹(𝒪)` on `ℙ¹`.
* `IsCanonicalDivisor.degree_eq_two_mul_finrank_divisorCechCohomology_zero_one_sub_two_of_sphere`:
  every canonical divisor `K` of `ℙ¹` has `deg K = 2 h¹(𝒪) - 2`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17.
-/

public section

open OnePoint Opposite
open TauCeti.AlgebraicGeometry

namespace TauCeti.RiemannSurface

/-- On `ℙ¹` the canonical divisor `-2[∞]` (`isCanonicalDivisor_neg_two_infty`) has
`h⁰(K) = h¹(𝒪)`, both being zero. -/
theorem
    finrank_divisorSheaf_neg_two_infty_globalSections_eq_finrank_divisorCechCohomology_zero_one :
    Module.finrank ℂ
        ((divisorSheaf ((-2 : ℤ) • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op ⊤)) =
      Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor (OnePoint ℂ)) 1) := by
  rw [finrank_divisorSheaf_zsmul_ofPoint_globalSections_sphere,
    finrank_divisorCechCohomology_zero_one_sphere]
  rfl

namespace IsCanonicalDivisor

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
