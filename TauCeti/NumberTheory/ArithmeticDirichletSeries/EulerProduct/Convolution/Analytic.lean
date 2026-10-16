/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Convolution.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# Analytic multiplication of ideal Euler factors

Ideal Dirichlet convolution multiplies evaluated Euler factors wherever both local series
converge absolutely. The local statement needs convergence only at the specified prime,
and includes boundary points of convergence. Absolute convergence over all nonzero ideals
then gives an unrestricted product of the convolution's Euler factors, with value the product
of the two original Dirichlet series.

The algebraic bridge is Mathlib's algebra homomorphism `ArithmeticFunction.ofPowerSeries`;
evaluation uses `ArithmeticFunction.LSeries_mul'`. Thus the formal Cauchy-product identity
for the local series is transported through the existing arithmetic-function API.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, for ideal Euler products.
* Mathlib's `ArithmeticFunction.ofPowerSeries` and `ArithmeticFunction.LSeries_mul'`.
-/

public section

namespace TauCeti

open IsDedekindDomain
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace IdealArithmeticFunction

/-- Ideal convolution multiplies the evaluated local arithmetic factors wherever both local
Dirichlet series converge absolutely, without requiring multiplicativity. -/
theorem LSeries_localArithmeticFactor_convolution (f g : IdealArithmeticFunction K)
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hf : LSeriesSummable (f.localArithmeticFactor P) s)
    (hg : LSeriesSummable (g.localArithmeticFactor P) s) :
    LSeries ((f.convolution g).localArithmeticFactor P) s =
      LSeries (f.localArithmeticFactor P) s * LSeries (g.localArithmeticFactor P) s := by
  rw [localArithmeticFactor_convolution]
  exact ArithmeticFunction.LSeries_mul' hf hg

end IdealArithmeticFunction

namespace EulerProductData

/-- Convolution multiplies evaluated Euler factors wherever the two local Dirichlet series
converge absolutely. No convergence at other primes is required. -/
@[simp]
theorem eulerFactor_convolution (D E : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hD : LSeriesSummable (D.localArithmeticFactor P) s)
    (hE : LSeriesSummable (E.localArithmeticFactor P) s) :
    (D.convolution E).eulerFactor P s = D.eulerFactor P s * E.eulerFactor P s := by
  simp only [eulerFactor_def, localArithmeticFactor_eq,
    toIdealArithmeticFunction_convolution] at hD hE ⊢
  exact IdealArithmeticFunction.LSeries_localArithmeticFactor_convolution
    D.toIdealArithmeticFunction E.toIdealArithmeticFunction P hD hE

/-- The Euler factors of a convolution have an unrestricted product equal to the product of
the original norm-regrouped Dirichlet series, whenever both ideal-indexed series converge
absolutely. -/
theorem hasProd_eulerFactor_convolution (D E : EulerProductData K) {s : ℂ}
    (hD : Summable (idealTerm K D.toIdealArithmeticFunction s))
    (hE : Summable (idealTerm K E.toIdealArithmeticFunction s)) :
    HasProd (fun P ↦ (D.convolution E).eulerFactor P s)
      (LSeries (normCoeff K D.toIdealArithmeticFunction) s *
        LSeries (normCoeff K E.toIdealArithmeticFunction) s) := by
  convert (D.hasProd_eulerFactor hD).mul (E.hasProd_eulerFactor hE) using 1
  ext P
  exact eulerFactor_convolution D E P
    (D.LSeriesSummable_localArithmeticFactor hD P)
    (E.LSeriesSummable_localArithmeticFactor hE P)

end EulerProductData

end TauCeti
