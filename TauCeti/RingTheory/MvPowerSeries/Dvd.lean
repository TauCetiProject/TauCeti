/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Divisibility of multivariate power series by constants

A constant power series `C r` divides `f` exactly when `r` divides every coefficient of `f`. This
is the multivariate form of `PowerSeries.C_dvd_iff_dvd_coeff`, and the power-series form of
Mathlib's `MvPolynomial.C_dvd_iff_dvd_coeff`; the quotient is assembled from the infinitely many
coefficient quotients at once.

It turns a congruence of power series that holds coefficientwise modulo `r`, for instance one
proved after reducing the coefficients modulo `r`, into divisibility in the power series ring,
where it can be raised to powers.

## Main results

* `MvPowerSeries.C_dvd_iff_dvd_coeff`: `C r ∣ f ↔ ∀ d, r ∣ coeff d f`.
-/

public section

namespace MvPowerSeries

variable {σ R : Type*} [Semiring R]

/-- A constant power series `C r` divides `f` if and only if `r` divides every coefficient
of `f`. -/
theorem C_dvd_iff_dvd_coeff (r : R) (f : MvPowerSeries σ R) :
    C r ∣ f ↔ ∀ d, r ∣ coeff d f := by
  constructor
  · rintro ⟨g, rfl⟩ d
    rw [coeff_C_mul]
    exact dvd_mul_right r _
  · intro h
    choose c hc using h
    let g : MvPowerSeries σ R := c
    exact ⟨g, ext fun d ↦ by rw [coeff_C_mul, hc]; rfl⟩

end MvPowerSeries
