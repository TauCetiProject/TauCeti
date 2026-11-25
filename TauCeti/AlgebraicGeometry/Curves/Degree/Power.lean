/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Degree
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Degrees of tensor powers on integral proper curves

Let `X` be an integral scheme, proper over a field `k` with fibres of dimension at most one; the
curve may be singular. The Euler-characteristic degree of a tensor power `a ^ n` of a line-bundle
class is `n` times the degree of `a`, for natural and integer exponents. This follows from
additivity of degree (`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_mul_of_isIntegral`).

Unlike that additivity statement, the results here assume no finiteness of `H⁰(X, 𝒪_X)` or
`H¹(X, 𝒪_X)`: on a proper curve both are automatic
(`Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one`, proved with
the normalization of the curve). They therefore live with the curve theory rather than with the
general Cartier-divisor degree API.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pow_of_isIntegral` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_zpow_of_isIntegral`: the degree of a
  tensor power is the multiple of the degree.

## References

* [The Stacks Project, Section 33.44](https://stacks.math.columbia.edu/tag/0AYQ), *Degrees on
  curves*.
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]

namespace LineBundleClass

/-- The degree of a tensor power is the multiple of the degree, on an integral proper curve over
`k`. -/
@[simp]
theorem eulerDegree_pow_of_isIntegral (a : LineBundleClass X) (n : ℕ) :
    eulerDegree k (a ^ n) = n * eulerDegree k a := by
  have := Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k
    ((relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mp inferInstance)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, eulerDegree_mul_of_isIntegral, ih]
    push_cast
    ring

/-- The degree of an integer tensor power is the multiple of the degree, on an integral proper
curve over `k`. -/
@[simp]
theorem eulerDegree_zpow_of_isIntegral (a : LineBundleClass X) (n : ℤ) :
    eulerDegree k (a ^ n) = n * eulerDegree k a := by
  have := Scheme.Modules.finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one k
    ((relativeDimensionLE_iff_of_field (X ↘ Spec (.of k))).mp inferInstance)
  cases n with
  | ofNat n => simp
  | negSucc n =>
    rw [zpow_negSucc, eulerDegree_inv_of_isIntegral, eulerDegree_pow_of_isIntegral,
      Int.negSucc_eq]
    push_cast
    ring

end LineBundleClass

end TauCeti.AlgebraicGeometry
