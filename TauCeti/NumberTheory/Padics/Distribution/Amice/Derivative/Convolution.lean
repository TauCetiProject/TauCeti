/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Convolution
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Derivative

/-!
# The transpose derivative and convolution

The Amice transform turns convolution of locally analytic distributions into multiplication of
power series, and the transpose derivative `(d μ)(f) = μ(f')` into multiplication by
`log (1 + T)` (`TauCeti.LocallyAnalyticDistribution.amiceTransform_derivative`). Hence the
transpose derivative commutes with convolution, `d (μ * ν) = d μ * ν`, and is convolution with the
derivative at `0`, `d 1 : f ↦ f'(0)`, whose Amice transform is `log (1 + T)`
(`amiceTransform_derivative_one`).

## Main results

* `TauCeti.LocallyAnalyticDistribution.derivative_mul_eq_derivative_left_mul`: the transpose
  derivative commutes with convolution, `d (μ * ν) = d μ * ν`.
* `TauCeti.LocallyAnalyticDistribution.derivative_eq_derivative_one_mul`: the transpose derivative
  is convolution with `d 1`.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_derivative_one`: the derivative at `0` has
  Amice transform `log (1 + T)`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
-/

public section

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace LocallyAnalyticDistribution

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- **The transpose derivative commutes with convolution**: `d (μ * ν) = d μ * ν`. -/
theorem derivative_mul_eq_derivative_left_mul (μ ν : LocallyAnalyticDistribution p K) :
    derivative (μ * ν) = derivative μ * ν :=
  amiceTransform_injective (by simp [mul_assoc])

/-- The transpose derivative is convolution with `d 1`, the derivative at `0`. -/
theorem derivative_eq_derivative_one_mul (μ : LocallyAnalyticDistribution p K) :
    derivative μ = derivative 1 * μ := by
  rw [← derivative_mul_eq_derivative_left_mul, one_mul]

/-- The transpose derivative of the unit `1 = δ_0` of the convolution algebra is the derivative at
`0`, `f ↦ f'(0)`; its Amice transform is `log (1 + T)`. -/
theorem amiceTransform_derivative_one :
    amiceTransform (derivative (1 : LocallyAnalyticDistribution p K)) = PowerSeries.log K := by
  rw [amiceTransform_derivative, amiceTransform_one, mul_one]

end LocallyAnalyticDistribution

end TauCeti
