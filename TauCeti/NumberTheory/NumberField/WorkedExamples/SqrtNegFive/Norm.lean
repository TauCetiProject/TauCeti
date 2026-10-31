/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.IntervalCases
import TauCeti.Algebra.QuadraticAlgebra.Discriminant

/-!
# Norm arithmetic of `ℤ[√-5]`

The norm form of `ℤ[√-5] = QuadraticAlgebra ℤ (-5) 0` is `a² + 5 b²`. It is nonnegative
(`QuadraticAlgebra.norm_nonneg_of_discr_nonpos`) and never takes the value `2`, so an element whose
norm divides `2` is a unit. These are the norm inputs to the class-number and unique-factorization
arguments for `ℚ(√-5)`.

## Main results

* `QuadraticAlgebra.norm_eq_re_sq_add_five_mul_im_sq`: the norm of `a + b √-5` is `a² + 5 b²`.
* `QuadraticAlgebra.norm_neg_five_ne_two`: no element of `ℤ[√-5]` has norm `2`.
* `TauCeti.NumberField.SqrtNegFive.isUnit_of_norm_dvd_two`: an element of `ℤ[√-5]` whose norm
  divides `2` is a unit.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §5.
-/

public section

namespace QuadraticAlgebra

/-- The norm form of `ℤ[√-5]` is `a² + 5 b²`. -/
theorem norm_eq_re_sq_add_five_mul_im_sq (z : QuadraticAlgebra ℤ (-5) 0) :
    z.norm = z.re ^ 2 + 5 * z.im ^ 2 := by
  rw [norm_def]
  ring

/-- No element of `ℤ[√-5]` has norm `2`. -/
theorem norm_neg_five_ne_two (z : QuadraticAlgebra ℤ (-5) 0) : z.norm ≠ 2 := by
  rw [norm_eq_re_sq_add_five_mul_im_sq]
  intro h
  have him : z.im = 0 := by
    have : z.im ^ 2 < 1 := by nlinarith [sq_nonneg z.re]
    rw [sq_lt_one_iff_abs_lt_one, abs_lt] at this
    omega
  rw [him] at h
  have h1 : -2 < z.re := by nlinarith
  have h2 : z.re < 2 := by nlinarith
  interval_cases z.re <;> norm_num at h

end QuadraticAlgebra

open QuadraticAlgebra

namespace TauCeti.NumberField.SqrtNegFive

/-- An element of `ℤ[√-5]` whose norm divides `2` is a unit: its norm is `1`. -/
theorem isUnit_of_norm_dvd_two {z : QuadraticAlgebra ℤ (-5) 0} (h : z.norm ∣ 2) :
    IsUnit z := by
  have h0 : z.norm ≠ 0 := by
    rintro h0
    rw [h0, zero_dvd_iff] at h
    norm_num at h
  have hle := Int.le_of_dvd (by norm_num) h
  have hge := norm_nonneg_of_discr_nonpos (by norm_num [discr_def]) z
  have h2 := norm_neg_five_ne_two z
  have h1 : z.norm = 1 := by omega
  rw [isUnit_iff_norm_isUnit, h1]
  exact isUnit_one

end TauCeti.NumberField.SqrtNegFive
