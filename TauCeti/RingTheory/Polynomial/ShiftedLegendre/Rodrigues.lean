/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Rodrigues' formula for the Legendre polynomials in the variable `x`

Mathlib's `Polynomial.shiftedLegendre n` is the shifted Legendre polynomial `P*ₙ(y)`, with
Rodrigues' formula `n! P*ₙ = (d/dy)ⁿ (yⁿ (1 - y)ⁿ)` (`Polynomial.factorial_mul_shiftedLegendre_eq`).
The Legendre polynomial is `Pₙ(x) = P*ₙ((1 - x)/2)`. This file transports Rodrigues' formula to
the variable `x`, over any commutative ring in which `2` is invertible:

  `(d/dx)ⁿ (x² - 1)ⁿ = 2ⁿ n! Pₙ(x)`  (DLMF 14.7.13 at `m = 0`, DLMF 18.5.5 for `α = β = 0`),

and records the values `P*ₙ(0) = 1` and `P*ₙ(1) = (-1)ⁿ`, that is `Pₙ(1) = 1` and
`Pₙ(-1) = (-1)ⁿ`.

## Main results

* `Polynomial.eval_zero_shiftedLegendre`, `Polynomial.eval_one_shiftedLegendre`: the values at
  `0` and `1`.
* `Polynomial.iterate_derivative_X_sq_sub_one_pow`: Rodrigues' formula in the variable `x`.

The formula is the polynomial form of `iteratedDeriv_legendreRodrigues_numerator` in lean-DLMF
(`DLMF/OrthogonalPolynomials/LegendreComplexLaplace.lean`), which proves it for its own Legendre
polynomial by analytic continuation; the proof here is algebraic, by the substitution
`y = (1 - x)/2`.
-/

public section

open Nat

namespace Polynomial

/-- The shifted Legendre polynomial takes the value `1` at `0`, that is `Pₙ(1) = 1`. -/
@[simp]
theorem eval_zero_shiftedLegendre (n : ℕ) : (shiftedLegendre n).eval 0 = 1 := by
  simp [← coeff_zero_eq_eval_zero, coeff_shiftedLegendre]

/-- The shifted Legendre polynomial takes the value `(-1)ⁿ` at `1`, that is `Pₙ(-1) = (-1)ⁿ`. -/
@[simp]
theorem eval_one_shiftedLegendre (n : ℕ) : (shiftedLegendre n).eval 1 = (-1) ^ n := by
  simpa using shiftedLegendre_eval_symm n (1 : ℤ)

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- **Rodrigues' formula** in the variable `x` (DLMF 14.7.13 at `m = 0`):
`(d/dx)ⁿ (x² - 1)ⁿ = 2ⁿ n! Pₙ(x)`, where `Pₙ(x) = P*ₙ((1 - x)/2)` is the shifted Legendre
polynomial `shiftedLegendre n` composed with `(1 - X)/2`. -/
theorem iterate_derivative_X_sq_sub_one_pow (n : ℕ) :
    derivative^[n] ((X ^ 2 - 1 : R[X]) ^ n) =
      C (2 ^ n * n ! : R) * ((shiftedLegendre n).map (Int.castRingHom R)).comp
        (C ⅟2 * (1 - X)) := by
  have h2 : (C ⅟2 : R[X]) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul, invOf_mul_self, C_1]
  have hq : (C ⅟2 * (1 - X) : R[X]) = C (-⅟2) * X + C ⅟2 := by
    rw [C_neg]; ring
  -- `x² - 1 = -4 y (1 - y)` for `y = (1 - x)/2`.
  have hF : (X ^ 2 - 1 : R[X]) ^ n =
      C ((-4 : R) ^ n) * (X ^ n * (1 - X) ^ n : R[X]).comp (C ⅟2 * (1 - X)) := by
    have h4 : (X ^ 2 - 1 : R[X]) = C (-4) * (C ⅟2 * (1 - X) * (1 - C ⅟2 * (1 - X))) := by
      rw [map_neg, map_ofNat]
      linear_combination (-(2 * C ⅟2 + 1) * (1 - X) ^ 2 + 2 * (1 - X)) * h2
    rw [h4, mul_pow, mul_pow, C_pow]
    simp only [mul_comp, pow_comp, X_comp, sub_comp, one_comp]
  have hR : derivative^[n] (X ^ n * (1 - X) ^ n : R[X]) =
      C (n ! : R) * (shiftedLegendre n).map (Int.castRingHom R) := by
    have := congrArg (map (Int.castRingHom R)) (factorial_mul_shiftedLegendre_eq n)
    rw [Polynomial.map_mul, ← iterate_derivative_map] at this
    simpa using this.symm
  have hc : ((-4 : R) * -⅟2) = 2 := by
    linear_combination (2 : R) * (invOf_mul_self (2 : R))
  rw [hF, iterate_derivative_C_mul, hq, iterate_derivative_comp_C_mul_X_add_C, hR, ← hq]
  simp only [mul_comp, C_comp, ← mul_assoc, ← C_mul, ← mul_pow, hc]

end Polynomial
