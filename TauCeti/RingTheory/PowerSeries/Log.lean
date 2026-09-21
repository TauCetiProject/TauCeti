/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Formal logarithmic derivatives of power series

For a power series `f` with constant coefficient one, Mathlib's `PowerSeries.logOf f` is the
formal expansion of `log f`. This file defines its formal derivative and records the
characteristic identity

`logDeriv f * f = derivative f`.

Thus over a field it is the usual quotient `f' / f`. The multiplicative identity is more general:
it needs only a commutative ring over the rationals, because the constant coefficient one makes
`f - 1` a valid substitution into the logarithm series.

## Main definitions

* `PowerSeries.logDeriv`: the formal derivative of `PowerSeries.logOf`.
* `PowerSeries.coeff_logDeriv`: the coefficient formula for the formal logarithmic derivative.
* `PowerSeries.logDeriv_mul`: the product identity characterizing the logarithmic derivative.
* `PowerSeries.logDeriv_eq_derivative_mul_inv`: the quotient form over a field.
-/

public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The **formal logarithmic derivative** of a power series: the derivative of
`PowerSeries.logOf f`. When `f` has constant coefficient one, this is characterized by
`PowerSeries.logDeriv_mul`. -/
noncomputable def logDeriv (f : A⟦X⟧) : A⟦X⟧ :=
  d⁄dX A (logOf f)

/-- Coefficients of the formal logarithmic derivative are the shifted coefficients of the formal
logarithm, multiplied by their positive degree. -/
theorem coeff_logDeriv (f : A⟦X⟧) (n : ℕ) :
    coeff n (logDeriv f) = coeff (n + 1) (logOf f) * (n + 1) := by
  rw [logDeriv, coeff_derivative]

/-- The formal logarithmic derivative of a power series with constant coefficient one satisfies
`(log f)' * f = f'`. -/
theorem logDeriv_mul (f : A⟦X⟧) (hf : constantCoeff f = 1) :
    logDeriv f * f = d⁄dX A f := by
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [logDeriv, logOf_eq, derivative_subst hsub]
  have hlog := congrArg (substAlgHom hsub)
    (derivative_log_mul_one_add_X (A := A))
  simp only [map_mul, map_one, coe_substAlgHom] at hlog
  have hone : (1 : A⟦X⟧).subst (f - 1) = 1 := by
    rw [← coe_substAlgHom hsub, map_one]
  have hadd : (1 + X : A⟦X⟧).subst (f - 1) = f := by
    rw [subst_add hsub, subst_X hsub]
    rw [hone]
    ring
  rw [hadd] at hlog
  have hderiv : d⁄dX A (f - 1) = d⁄dX A f := by
    rw [map_sub, derivative_one, sub_zero]
  rw [hderiv]
  calc
    subst (f - 1) (d⁄dX A (log A)) * d⁄dX A f * f =
        (subst (f - 1) (d⁄dX A (log A)) * f) * d⁄dX A f := by ring
    _ = d⁄dX A f := by rw [hlog, one_mul]

/-- Over a field, the formal logarithmic derivative of a power series with constant coefficient
one is the quotient `f' / f`. -/
theorem logDeriv_eq_derivative_mul_inv {k : Type*} [Field k] [Algebra ℚ k]
    (f : k⟦X⟧) (hf : constantCoeff f = 1) :
    logDeriv f = d⁄dX k f * f⁻¹ := by
  have hunit : IsUnit f := isUnit_iff_constantCoeff.mpr (hf ▸ isUnit_one)
  apply hunit.mul_right_cancel
  rw [logDeriv_mul f hf, mul_assoc, f.inv_mul_cancel (by simp [hf]), mul_one]

end PowerSeries
