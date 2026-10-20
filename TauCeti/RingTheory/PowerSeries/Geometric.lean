/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The geometric series in `a X`

Mathlib's `PowerSeries.mk_one_mul_one_sub_eq_one` says that `∑ Xⁿ` inverts `1 - X`.  Rescaling
`X` by an element `a` of the coefficient ring turns it into the statement that the geometric
series `∑ aⁿ Xⁿ` inverts `1 - a X`, with no invertibility assumption on `a`.  This is the
one-variable factor of the generating functions of the complete homogeneous symmetric
polynomials, `∏ᵢ (1 - xᵢ X)⁻¹ = ∑ₙ hₙ Xⁿ`.

Its square `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ` inverts `(1 - X) ^ 2`. Dividing a polynomial `p` by
`(1 - X) ^ 2` therefore produces coefficients which, beyond the degree of `p`, are the values
`(n + 1) p (1) - p' (1)` of an affine function of `n`. This is the shape of the coefficients of the
Lefschetz zeta function `det (1 - t P) / (1 - t) ^ 2` of an orientation-preserving map of a closed
connected oriented surface acting by `P` on its first cohomology.

## Main results

* `TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one`:
  `(∑ aⁿ Xⁿ) * (1 - a X) = 1`.
* `Polynomial.coeff_coe_mul_mk_one_sq`: the `a`-th coefficient of `p / (1 - X) ^ 2` is
  `(a + 1) p (1) - p' (1)` once `p` has degree at most `a + 1`.
-/

public section

namespace TauCeti

/-- **The geometric series in `a X`**: `∑ aⁿ Xⁿ` is a multiplicative inverse of `1 - a X`, for
every element `a` of the coefficient ring. -/
theorem powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one {R : Type*} [Ring R] (a : R) :
    PowerSeries.mk (fun n => a ^ n) *
        (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one, ← mul_assoc, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]

open Polynomial in
/-- The `a`-th coefficient of `p / (1 - X) ^ 2 = p * (∑ Xⁿ) ^ 2` is `(a + 1) p (1) - p' (1)`
whenever the polynomial `p` has degree at most `a + 1`. -/
theorem _root_.Polynomial.coeff_coe_mul_mk_one_sq {R : Type*} [CommRing R] (p : R[X]) {a : ℕ}
    (hp : p.natDegree ≤ a + 1) :
    PowerSeries.coeff a ((p : PowerSeries R) * PowerSeries.mk 1 ^ 2) =
      (a + 1) * p.eval 1 - p.derivative.eval 1 := by
  have h2 : (PowerSeries.mk 1 : PowerSeries R) ^ 2 = PowerSeries.mk fun n ↦ (n + 1 : R) := by
    rw [show 2 = 1 + 1 from rfl, PowerSeries.mk_one_pow_eq_mk_choose_add]
    ext n
    simp [add_comm]
  have hlt : p.natDegree < a + 2 := by omega
  rw [h2, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ _ (a + 1)]
  simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk, one_pow, mul_one]
  rw [Nat.cast_add_one, mul_comm (p.coeff (a + 1)), sub_self, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
  ring

end TauCeti
