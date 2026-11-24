/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
-- Proof-only: the multivariate statement, specialised to one variable.
import TauCeti.RingTheory.MvPowerSeries.Dvd

/-!
# Divisibility of power series by constants and polynomial factors

A constant power series `C r` divides `f` exactly when `r` divides every coefficient of `f`. This
is the power-series form of Mathlib's `Polynomial.C_dvd_iff_dvd_coeff` and
`MvPolynomial.C_dvd_iff_dvd_coeff`, and the one-variable case of
`MvPowerSeries.C_dvd_iff_dvd_coeff`.

It is the step that removes a common power of a uniformiser from the coefficients of a power
series over a discrete valuation ring before applying Weierstrass preparation.

Over a commutative ring, `C r` divides `f` exactly when `f` vanishes in `(R ⧸ (r))⟦X⟧`.
Multiplication by `C r` is injective exactly when multiplication by `r` is.

This file also records basic unit facts for polynomial factors of formal power series with
constant term `1`: any polynomial factor `Q` of such a power series has unit constant term, and over
a field it has unit leading coefficient.

## Main results

* `PowerSeries.C_dvd_iff_dvd_coeff`: `C r ∣ f ↔ ∀ n, r ∣ coeff n f`.
* `PowerSeries.C_dvd_iff_map_mk_eq_zero`: `C r` divides `f` if and only if `f` vanishes in
  `(R ⧸ (r))⟦X⟧`.
* `PowerSeries.isSMulRegular_C_iff`: `C r` is a nonzerodivisor of `R⟦X⟧` if and only if `r` is
  one of `R`.
* `PowerSeries.isUnit_coeff_zero_of_eq_coe_mul`: a polynomial factor of a power series with
  constant term `1` has unit constant term.
* `PowerSeries.isUnit_leadingCoeff_of_eq_coe_mul`: over a field, a polynomial factor of a power
  series with constant term `1` has unit leading coefficient.
-/

public section

namespace PowerSeries

section ConstDvd

variable {R : Type*} [Semiring R]

/-- A constant power series `C r` divides `f` if and only if `r` divides every coefficient
of `f`. -/
theorem C_dvd_iff_dvd_coeff (r : R) (f : R⟦X⟧) : C r ∣ f ↔ ∀ n, r ∣ coeff n f := by
  rw [C_apply, MvPowerSeries.C_dvd_iff_dvd_coeff]
  refine ⟨fun h n ↦ ?_, fun h d ↦ ?_⟩
  · rw [coeff_def Finsupp.single_eq_same]
    exact h _
  · rw [← coeff_def (s := d) (n := d ()) rfl]
    exact h (d ())

/-- Multiplication by a constant series `C r` is injective if and only if multiplication by `r`
is. -/
@[simp]
theorem isSMulRegular_C_iff {r : R} : IsSMulRegular R⟦X⟧ (C r) ↔ IsSMulRegular R r := by
  refine ⟨fun h a b hab ↦ C_injective (h ?_), fun h f g hfg ↦ ext fun n ↦ h ?_⟩
  · simpa only [smul_eq_mul, ← map_mul] using congrArg C hab
  · simpa only [smul_eq_mul, coeff_C_mul] using congrArg (coeff n) hfg

/-- A constant series `C r` divides `f` if and only if `f` vanishes modulo `r`. -/
theorem C_dvd_iff_map_mk_eq_zero {R : Type*} [CommRing R] {r : R} {f : R⟦X⟧} :
    C r ∣ f ↔ map (Ideal.Quotient.mk (Ideal.span {r})) f = 0 := by
  simp [C_dvd_iff_dvd_coeff, PowerSeries.ext_iff, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

end ConstDvd

section PolynomialFactor

/-- If a power series with constant term `1` factors as `Q * S` with `Q` a polynomial, then `Q`
has unit constant term. -/
theorem isUnit_coeff_zero_of_eq_coe_mul {R : Type*} [CommSemiring R] {u_series : R⟦X⟧}
    (hu0 : constantCoeff u_series = 1) {Q : Polynomial R} {S : R⟦X⟧}
    (hQS : u_series = (Q : R⟦X⟧) * S) : IsUnit (Q.coeff 0) := by
  refine IsUnit.of_mul_eq_one (constantCoeff S) ?_
  have h0 := congrArg constantCoeff hQS
  simpa [hu0] using h0.symm

/-- Over a field, a polynomial factor of a power series with constant term `1` has unit leading
coefficient. -/
theorem isUnit_leadingCoeff_of_eq_coe_mul {K : Type*} [Field K] {u_series : K⟦X⟧}
    (hu0 : constantCoeff u_series = 1) {Q : Polynomial K} {S : K⟦X⟧}
    (hQS : u_series = (Q : K⟦X⟧) * S) : IsUnit Q.leadingCoeff :=
  (Polynomial.leadingCoeff_ne_zero.mpr fun h ↦ by
    simpa [h] using isUnit_coeff_zero_of_eq_coe_mul hu0 hQS).isUnit

end PolynomialFactor

end PowerSeries
