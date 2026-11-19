/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# Euler products of Dirichlet series with completely multiplicative coefficients

Where the Dirichlet series of a completely multiplicative arithmetic function `f` converges
absolutely, it is the Euler product `L(f, s) = ∏_p (1 - f p * p ^ (-s))⁻¹`. This is the case
`c = 0` of the Euler product with quadratic local factors,
`TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`.

## Main results

* `ArithmeticFunction.IsCompletelyMultiplicative.LSeries_eulerProduct_hasProd`: the Euler
  product, as a `HasProd`.
* `ArithmeticFunction.IsCompletelyMultiplicative.LSeries_eulerProduct_tprod`: the same, as an
  equality with `∏'`.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, Undergraduate Texts in Mathematics,
  Springer, 1976, Chapter 11 (Euler products).
* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem and More*, blueprint,
  Theorems 9.1.66–9.1.67.
-/

public section

open Nat

namespace ArithmeticFunction.IsCompletelyMultiplicative

variable {f : ArithmeticFunction ℂ} {s : ℂ}

/-- **The Euler product of a Dirichlet series** with completely multiplicative coefficients, as
a `HasProd`: where the series converges absolutely, `∏' p, (1 - f p * p ^ (-s))⁻¹ = L(f, s)`. -/
theorem LSeries_eulerProduct_hasProd (hf : f.IsCompletelyMultiplicative)
    (hs : LSeriesSummable (⇑f) s) :
    HasProd (fun p : Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) (LSeries (⇑f) s) := by
  simpa using TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence (c := 0) hf.map_one
    (fun {m n} _ _ _ ↦ hf.map_mul m n)
    (fun p _ r ↦ by simp only [hf.map_pow, Pi.zero_apply, zero_mul, sub_zero]; ring) hs

/-- **The Euler product of a Dirichlet series** with completely multiplicative coefficients:
where the series converges absolutely, `∏' p, (1 - f p * p ^ (-s))⁻¹ = L(f, s)`. -/
theorem LSeries_eulerProduct_tprod (hf : f.IsCompletelyMultiplicative)
    (hs : LSeriesSummable (⇑f) s) :
    ∏' p : Primes, (1 - f p * (p : ℂ) ^ (-s))⁻¹ = LSeries (⇑f) s :=
  (hf.LSeries_eulerProduct_hasProd hs).tprod_eq

end ArithmeticFunction.IsCompletelyMultiplicative
