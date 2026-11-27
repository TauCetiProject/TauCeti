/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.Algebra.Polynomial.ExpTwistDeriv
public import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Derivatives of exponential polynomials

Over a commutative `ℚ`-algebra, differentiating an exponential polynomial `P(X) e^{cX}` gives
`(P' + c P) e^{cX}`, so its `m`-th derivative is `(expTwistDeriv c m P)(X) e^{cX}`, where
`Polynomial.expTwistDeriv c m = (d/dX + c) ^ m`.

## Main results

* `PowerSeries.iterate_derivative_coe_mul_rescale_exp`: the `m`-th derivative of `P(X) e^{cX}` is
  `(expTwistDeriv c m P)(X) e^{cX}`.
-/

public section

namespace PowerSeries

/-- **Derivatives of an exponential polynomial**: over a commutative `ℚ`-algebra, the `m`-th
derivative of `P(X) e^{cX}` is `(expTwistDeriv c m P)(X) e^{cX}`, where
`expTwistDeriv c m = (d/dX + c) ^ m`. -/
theorem iterate_derivative_coe_mul_rescale_exp {R : Type*} [CommRing R] [Algebra ℚ R] (c : R)
    (m : ℕ) (P : Polynomial R) :
    d⁄dX^[m] ((P : R⟦X⟧) * rescale c (exp R)) =
      (Polynomial.expTwistDeriv c m P : R⟦X⟧) * rescale c (exp R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, derivative_rescale, derivative_exp,
      derivative_coe, Polynomial.expTwistDeriv_succ, Polynomial.coe_add, Polynomial.smul_eq_C_mul,
      Polynomial.coe_mul, Polynomial.coe_C, smul_eq_mul, smul_eq_mul]
    ring

end PowerSeries
