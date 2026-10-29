/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Divisibility of power series by constants

A constant power series `C r` divides `f` exactly when `r` divides every coefficient of `f`. This
is the power-series form of Mathlib's `Polynomial.C_dvd_iff_dvd_coeff` and
`MvPolynomial.C_dvd_iff_dvd_coeff`; unlike the polynomial case, the quotient is assembled from
infinitely many coefficient quotients at once, which `PowerSeries.mk` allows directly.

It is the step that removes a common power of a uniformiser from the coefficients of a power
series over a discrete valuation ring before applying Weierstrass preparation.

## Main results

* `PowerSeries.C_dvd_iff_dvd_coeff`: `C r ∣ f ↔ ∀ n, r ∣ coeff n f`.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- A constant power series `C r` divides `f` if and only if `r` divides every coefficient
of `f`. -/
theorem C_dvd_iff_dvd_coeff (r : R) (f : R⟦X⟧) : C r ∣ f ↔ ∀ n, r ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right r _
  · intro h
    choose c hc using h
    exact ⟨mk c, ext fun n ↦ by rw [coeff_C_mul, coeff_mk, hc]⟩

end PowerSeries
