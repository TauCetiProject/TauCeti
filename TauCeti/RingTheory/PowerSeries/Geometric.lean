/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.PowerSeries.WellKnown
import TauCeti.Algebra.BigOperators.Finset.Range

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
* `TauCeti.powerSeries_one_sub_C_mul_X_mul_mk_sum_smul_pow`,
  `TauCeti.powerSeries_mk_sum_smul_pow_mul_one_sub_C_mul_X`: for scalars `c k` in a commutative
  ring `R` and an element `a` of an `R`-algebra, multiplying the series with coefficients
  `∑ k ∈ range (m + 1), c k • a ^ (m - k)` by `1 - a X`, on either side, gives `∑ c k Xᵏ`.
  This series is the product of `∑ c k Xᵏ` with the geometric series `∑ aⁿ Xⁿ`.
* `PowerSeries.mk_one_sq`: `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ`.
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

/-- **Convolution with the geometric series.** For scalars `c k` and an element `a` of an
algebra, the series with coefficients `∑ k ∈ range (m + 1), c k • a ^ (m - k)` is carried by
`1 - a X`, multiplying on the left, to the series `∑ c k Xᵏ`. -/
theorem powerSeries_one_sub_C_mul_X_mul_mk_sum_smul_pow {R A : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] (c : ℕ → R) (a : A) :
    (1 - PowerSeries.C a * PowerSeries.X) *
        PowerSeries.mk (fun m ↦ ∑ k ∈ Finset.range (m + 1), c k • a ^ (m - k)) =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk c) := by
  ext (_ | m)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, sum_range_succ_smul_pow_sub,
      Algebra.algebraMap_eq_smul_one]

/-- **Convolution with the geometric series.** For scalars `c k` and an element `a` of an
algebra, the series with coefficients `∑ k ∈ range (m + 1), c k • a ^ (m - k)` is carried by
`1 - a X`, multiplying on the right, to the series `∑ c k Xᵏ`. -/
theorem powerSeries_mk_sum_smul_pow_mul_one_sub_C_mul_X {R A : Type*} [CommSemiring R] [Ring A]
    [Algebra R A] (c : ℕ → R) (a : A) :
    PowerSeries.mk (fun m ↦ ∑ k ∈ Finset.range (m + 1), c k • a ^ (m - k)) *
        (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk c) := by
  ext (_ | m)
  · simp [Algebra.algebraMap_eq_smul_one]
  · simp [mul_sub, ← mul_assoc, PowerSeries.coeff_succ_mul_X, sum_range_succ_smul_pow_sub',
      Algebra.algebraMap_eq_smul_one]

/-- The square of the geometric series: `(∑ Xⁿ) ^ 2 = ∑ (n + 1) Xⁿ`. -/
theorem _root_.PowerSeries.mk_one_sq (R : Type*) [CommRing R] :
    (PowerSeries.mk 1 : PowerSeries R) ^ 2 = PowerSeries.mk fun n ↦ (n + 1 : R) := by
  rw [← one_add_one_eq_two, PowerSeries.mk_one_pow_eq_mk_choose_add]
  ext n
  simp [add_comm]

open Polynomial in
/-- The `a`-th coefficient of `p / (1 - X) ^ 2 = p * (∑ Xⁿ) ^ 2` is `(a + 1) p (1) - p' (1)`
whenever the polynomial `p` has degree at most `a + 1`. -/
theorem _root_.Polynomial.coeff_coe_mul_mk_one_sq {R : Type*} [CommRing R] (p : R[X]) {a : ℕ}
    (hp : p.natDegree ≤ a + 1) :
    PowerSeries.coeff a ((p : PowerSeries R) * PowerSeries.mk 1 ^ 2) =
      (a + 1) * p.eval 1 - p.derivative.eval 1 := by
  have hlt : p.natDegree < a + 2 := by omega
  have h (i : ℕ) (hi : i ∈ Finset.range (a + 1)) :
      p.coeff i * ((a - i : ℕ) + 1) = (a + 1) * p.coeff i - p.coeff i * i := by
    rw [Nat.cast_sub (Finset.mem_range_succ_iff.1 hi)]
    ring
  rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt]
  simp [PowerSeries.mk_one_sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ _ (a + 1),
    Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end TauCeti
