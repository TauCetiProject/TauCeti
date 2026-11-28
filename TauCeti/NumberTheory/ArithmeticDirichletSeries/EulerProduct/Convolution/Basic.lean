/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution.Multiplicative
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Data

/-!
# Convolution of ideal Euler-product data

Ideal Dirichlet convolution multiplies the local power series, in contrast to pointwise
multiplication of ideal coefficients. This file lifts convolution to Euler-product data and
identifies its local series with products in `PowerSeries ℂ`. Together with the existing
`TauCeti.normCoeff_convolution`, this also identifies the regrouped coefficients with products
in Mathlib's Dirichlet-convolution ring `ArithmeticFunction ℂ`. The local arithmetic factors
also multiply in that ring, giving the algebraic input for multiplication of evaluated factors.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* Mathlib's `PowerSeries.coeff_mul` and `dvd_prime_pow`.
* Mathlib's algebra homomorphism `ArithmeticFunction.ofPowerSeries`.
-/

public section

namespace TauCeti

open IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

/-- The local prime-power series of a convolution is the product of the local series. -/
theorem localPowerSeries_convolution (f g : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (convolution f g).localPowerSeries P = f.localPowerSeries P * g.localPowerSeries P := by
  ext n
  simp only [coeff_localPowerSeries, PowerSeries.coeff_mul, convolution_primeIdealPow]

/-- Ideal convolution multiplies the local arithmetic factors in Mathlib's
Dirichlet-convolution ring. -/
@[simp]
theorem localArithmeticFactor_convolution (f g : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (convolution f g).localArithmeticFactor P =
      f.localArithmeticFactor P * g.localArithmeticFactor P := by
  simp only [localArithmeticFactor_def, localPowerSeries_convolution]
  exact (ArithmeticFunction.ofPowerSeries _).map_mul _ _

end IdealArithmeticFunction

namespace EulerProductData

/-- The ideal delta function, bundled as the identity for Euler-product convolution. -/
noncomputable def delta : EulerProductData K where
  toIdealArithmeticFunction := IdealArithmeticFunction.delta
  isMultiplicative := IdealArithmeticFunction.isMultiplicative_delta

/-- The underlying function of the bundled convolution identity is the ideal delta function. -/
@[simp]
theorem toIdealArithmeticFunction_delta :
    (delta : EulerProductData K).toIdealArithmeticFunction = IdealArithmeticFunction.delta :=
  (rfl)

/-- Convolve two ideal coefficient systems. This operation multiplies local series and is
distinct from the pointwise multiplication instance on `EulerProductData`. -/
noncomputable def convolution (D E : EulerProductData K) : EulerProductData K where
  toIdealArithmeticFunction := D.toIdealArithmeticFunction.convolution E.toIdealArithmeticFunction
  isMultiplicative := D.isMultiplicative.convolution E.isMultiplicative

/-- The underlying coefficient function of bundled convolution is ideal convolution. -/
@[simp]
theorem toIdealArithmeticFunction_convolution (D E : EulerProductData K) :
    (D.convolution E).toIdealArithmeticFunction =
      D.toIdealArithmeticFunction.convolution E.toIdealArithmeticFunction := (rfl)

/-- The ideal delta function is a left identity for bundled convolution. -/
@[simp]
theorem delta_convolution (D : EulerProductData K) : delta.convolution D = D := by
  apply ext
  exact congrFun (IdealArithmeticFunction.delta_convolution _)

/-- The ideal delta function is a right identity for bundled convolution. -/
@[simp]
theorem convolution_delta (D : EulerProductData K) : D.convolution delta = D := by
  apply ext
  exact congrFun (IdealArithmeticFunction.convolution_delta _)

/-- Bundled ideal convolution is commutative. -/
theorem convolution_comm (D E : EulerProductData K) : D.convolution E = E.convolution D := by
  apply ext
  exact congrFun (IdealArithmeticFunction.convolution_comm _ _)

/-- Bundled ideal convolution is associative. -/
theorem convolution_assoc (D E F : EulerProductData K) :
    (D.convolution E).convolution F = D.convolution (E.convolution F) := by
  apply ext
  exact congrFun (IdealArithmeticFunction.convolution_assoc _ _ _)

/-- Convolution multiplies the local power series of bundled Euler-product data. -/
@[simp]
theorem localPowerSeries_convolution (D E : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (D.convolution E).localPowerSeries P = D.localPowerSeries P * E.localPowerSeries P := by
  ext n
  simpa only [coeff_localPowerSeries, IdealArithmeticFunction.coeff_localPowerSeries,
    PowerSeries.coeff_mul, toIdealArithmeticFunction_convolution] using
      congrArg (PowerSeries.coeff n) (IdealArithmeticFunction.localPowerSeries_convolution
        D.toIdealArithmeticFunction E.toIdealArithmeticFunction P)

/-- Bundled convolution multiplies the local arithmetic factors in Mathlib's
Dirichlet-convolution ring. -/
@[simp]
theorem localArithmeticFactor_convolution (D E : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (D.convolution E).localArithmeticFactor P =
      D.localArithmeticFactor P * E.localArithmeticFactor P := by
  simp only [localArithmeticFactor_eq, toIdealArithmeticFunction_convolution,
    IdealArithmeticFunction.localArithmeticFactor_convolution]

end EulerProductData

end TauCeti
