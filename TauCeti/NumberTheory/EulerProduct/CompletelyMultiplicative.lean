/-
Copyright (c) 2023 Arend Mellendijk and The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
import TauCeti.NumberTheory.LSeries.EulerProduct

/-!
# Euler products of completely multiplicative functions

For a completely multiplicative arithmetic function `f`, each local factor of the Euler product
is geometric, so `∑ₙ f n = ∏ₚ (1 - f p)⁻¹` whenever the series converges absolutely, and likewise
`L(f, s) = ∏ₚ (1 - f p p⁻ˢ)⁻¹` at every point of absolute convergence of the L-series.

## Main results

* `ArithmeticFunction.IsCompletelyMultiplicative.eulerProduct_hasProd` and
  `ArithmeticFunction.IsCompletelyMultiplicative.eulerProduct_tprod`: the Euler product of a
  norm-summable completely multiplicative function.
* `ArithmeticFunction.IsCompletelyMultiplicative.LSeries_eulerProduct_hasProd` and
  `ArithmeticFunction.IsCompletelyMultiplicative.LSeries_eulerProduct_tprod`: the Euler product of
  its L-series, the case `c = 0` of `TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`.
-/

public section

open Nat

namespace ArithmeticFunction.IsCompletelyMultiplicative

section EulerProduct

variable {F : Type*} [NormedField F] [CompleteSpace F] {f : ArithmeticFunction F}

/-- The Euler product of a norm-summable completely multiplicative function, stated in terms
of `HasProd`. -/
theorem eulerProduct_hasProd (hf : f.IsCompletelyMultiplicative) (hsum : Summable (‖f ·‖)) :
    HasProd (fun p : Primes ↦ (1 - f p)⁻¹) (∑' n, f n) := by
  simpa using EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (f := hf.toMonoidWithZeroHom) (by simpa using hsum)

/-- The Euler product `∏ₚ (1 - f p)⁻¹ = ∑ₙ f n` of a norm-summable completely multiplicative
function. -/
theorem eulerProduct_tprod (hf : f.IsCompletelyMultiplicative) (hsum : Summable (‖f ·‖)) :
    ∏' p : Primes, (1 - f p)⁻¹ = ∑' n, f n :=
  (hf.eulerProduct_hasProd hsum).tprod_eq

end EulerProduct

section LSeries

open Complex

variable {f : ArithmeticFunction ℂ}

/-- The Euler product of the L-series of a completely multiplicative function, stated in terms
of `HasProd`. -/
theorem LSeries_eulerProduct_hasProd (hf : f.IsCompletelyMultiplicative) {s : ℂ}
    (hs : LSeriesSummable f s) :
    HasProd (fun p : Primes ↦ (1 - f p * (p : ℂ) ^ (-s))⁻¹) (LSeries f s) := by
  simpa using TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence (c := 0) hf.map_one
    (fun _ _ _ ↦ hf.map_mul _ _) (fun p _ r ↦ by
      rw [pow_succ' _ (r + 1), hf.map_mul]; simp) hs

/-- The Euler product `∏ₚ (1 - f p p⁻ˢ)⁻¹ = L(f, s)` of the L-series of a completely
multiplicative function at a point of absolute convergence. -/
theorem LSeries_eulerProduct_tprod (hf : f.IsCompletelyMultiplicative) {s : ℂ}
    (hs : LSeriesSummable f s) :
    ∏' p : Primes, (1 - f p * (p : ℂ) ^ (-s))⁻¹ = LSeries f s :=
  (hf.LSeries_eulerProduct_hasProd hs).tprod_eq

end LSeries

end ArithmeticFunction.IsCompletelyMultiplicative
