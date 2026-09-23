/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluating the Dickson polynomials of the second kind

The Eichler–Selberg weights `P_k(t, a)`, defined by
`∑_{k ≥ 2} P_k(t, a) x ^ (k - 2) = (1 - t x + a x²)⁻¹`, are the Dickson values
`(dickson 2 a (k - 2)).eval t`, so no new polynomial family is introduced for them. This file proves
the generating function and the closed forms the trace formula consumes. The central one is the
evaluation at a sum `x + y` with `x * y = a`: when `t` and `a` are the trace and determinant of a
`2 × 2` matrix with eigenvalues `x` and `y`, the weight `P_{n+2}(t, a)` is the trace of the matrix
on homogeneous polynomials of degree `n`.

## Main results

* `Polynomial.dickson_two_eval_add`: if `x * y = a`, then
  `(dickson 2 a n).eval (x + y) = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i)`.
* `Polynomial.dickson_two_eval_add_mul_sub`: if `x * y = a`, then
  `(dickson 2 a n).eval (x + y) * (x - y) = x ^ (n + 1) - y ^ (n + 1)`, the quotient formula with
  the division cleared.
* `Polynomial.dickson_two_sq_eval_two_mul`: `(dickson 2 (x ^ 2) n).eval (2 * x) = (n + 1) * x ^ n`,
  the repeated-root case `t² = 4 a`, where the quotient formula says nothing.
* `Polynomial.dickson_sq_mul_eval_mul`: for every kind `k`,
  `(dickson k (s ^ 2 * a) n).eval (s * t) = s ^ n * (dickson k a n).eval t`.
* `Polynomial.dickson_two_sq_eval_mul`:
  `(dickson 2 (s ^ 2) n).eval (s * t) = s ^ n * (Chebyshev.S R n).eval t`, the division-free form
  of `P_k(t, s²) = s ^ (k - 2) * U_{k-2}(t / (2 s))`.
* `Polynomial.mk_dickson_two_eval_mul_one_sub_add_eq_one`: the generating function
  `(∑ₙ (dickson 2 a n).eval t * Xⁿ) * (1 - t X + a X²) = 1`.

## References

* D. Zagier, *The Eichler–Selberg trace formula on `SL₂(ℤ)`*, appendix to S. Lang,
  *Introduction to Modular Forms*, Springer, 1976.
* A. Popa and D. Zagier, *A simple proof of the Eichler–Selberg trace formula*,
  J. Ramanujan Math. Soc. (2019), arXiv:1711.00327.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- **The Dickson polynomial of the second kind at `x + y` is the complete homogeneous symmetric
polynomial in `x` and `y`**, when its parameter is `x * y`.

When `x` and `y` are the eigenvalues of a `2 × 2` matrix, `x + y` and `x * y` are its trace and
determinant, and the right side is the trace of the matrix on homogeneous polynomials of degree
`n`; this is how the Eichler–Selberg weights enter as traces. The right side is the value of the
complete homogeneous symmetric polynomial `MvPolynomial.hsymm` at `![x, y]`, as computed by
`TauCeti.eval_hsymm_fin_two`. Compare Mathlib's
`dickson_one_one_eval_add_inv`, the first-kind analogue for `x * y = 1`, where the value is the
power sum `x ^ n + y ^ n`. -/
theorem dickson_two_eval_add {x y a : R} (h : x * y = a) (n : ℕ) :
    (dickson 2 a n).eval (x + y) = ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) := by
  subst h
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp [sum_range_succ, add_comm]
  | more n ih₀ ih₁ =>
    -- peel the top term off each complete homogeneous sum, `hₘ₊₁ = x ^ (m + 1) + y * hₘ`
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, ih₀, ih₁, Nat.add_sub_cancel,
      geom_sum₂_succ_eq x y (n := n + 1 + 1), geom_sum₂_succ_eq x y (n := n + 1)]
    ring

/-- **The Dickson value times `x - y` is `x ^ (n + 1) - y ^ (n + 1)`**, when `x * y = a`.

This is the quotient formula `P_k(t, a) = (x ^ (k - 1) - y ^ (k - 1)) / (x - y)` for the roots `x`,
`y` of `X² - t X + a`, stated multiplied out so that it holds in any commutative ring and at a
repeated root; for the value at a repeated root itself use `dickson_two_sq_eval_two_mul`, and for
the quotient itself, over a field at distinct roots, `dickson_two_eval_add_eq_div`. -/
theorem dickson_two_eval_add_mul_sub {x y a : R} (h : x * y = a) (n : ℕ) :
    (dickson 2 a n).eval (x + y) * (x - y) = x ^ (n + 1) - y ^ (n + 1) := by
  rw [dickson_two_eval_add h, ← geom_sum₂_mul, Nat.add_one_sub_one]

/-- **The quotient formula at distinct roots**: over a field, if `x * y = a` and `x ≠ y`, then
`(dickson 2 a n).eval (x + y) = (x ^ (n + 1) - y ^ (n + 1)) / (x - y)`. -/
theorem dickson_two_eval_add_eq_div {K : Type*} [Field K] {x y a : K} (h : x * y = a) (hxy : x ≠ y)
    (n : ℕ) : (dickson 2 a n).eval (x + y) = (x ^ (n + 1) - y ^ (n + 1)) / (x - y) :=
  eq_div_of_mul_eq (sub_ne_zero.mpr hxy) (dickson_two_eval_add_mul_sub h n)

/-- **At a repeated root the Dickson value is `(n + 1) * x ^ n`**: this is the value at `t = 2 * x`
with parameter `a = x ^ 2`, where `X² - t X + a = (X - x)²` has the repeated root `x`.

These are the `t² = 4 a` terms `P_k(2 x, x²) = (k - 1) * x ^ (k - 2)` of the Eichler–Selberg trace
formula, where `dickson_two_eval_add_mul_sub` degenerates to `0 = 0`. The other sign, `t = -2 * x`,
is the case `-x`, since `(-x) ^ 2 = x ^ 2`. -/
@[simp]
theorem dickson_two_sq_eval_two_mul (x : R) (n : ℕ) :
    (dickson 2 (x ^ 2) n).eval (2 * x) = (n + 1) * x ^ n := by
  rw [two_mul, dickson_two_eval_add (sq x).symm, ← Nat.cast_add_one]
  exact geom_sum₂_self x (n + 1)

/-- **The Dickson polynomials are homogeneous** of degree `n` when the parameter is given weight
two: for every kind `k`, scaling the argument by `s` and the parameter by `s ^ 2` scales the value
by `s ^ n`. -/
@[simp]
theorem dickson_sq_mul_eval_mul (k : ℕ) (s t a : R) (n : ℕ) :
    (dickson k (s ^ 2 * a) n).eval (s * t) = s ^ n * (dickson k a n).eval t := by
  induction n using Nat.twoStepInduction with
  | zero | one => simp
  | more n ih₀ ih₁ =>
    simp only [dickson_add_two, eval_sub, eval_mul, eval_X, eval_C, ih₀, ih₁]
    ring

/-- **The Dickson polynomial of the second kind with square parameter is a rescaled Chebyshev
polynomial**.

Since `Chebyshev.S R n` is `U_n(X / 2)`, this is the division-free form of the identity
`P_k(t, s²) = s ^ (k - 2) * U_{k-2}(t / (2 s))` relating the Eichler–Selberg weights to the
Chebyshev polynomials of the second kind; at `s = 1` it is Mathlib's
`dickson_two_one_eq_chebyshev_S` evaluated at `t`. For `Chebyshev.U` itself take `2 * t` for `t`:
`Chebyshev.S_comp_two_mul_X` and `eval_comp` turn `(Chebyshev.S R n).eval (2 * t)` into
`(Chebyshev.U R n).eval t` without inverting `2`. -/
@[simp]
theorem dickson_two_sq_eval_mul (s t : R) (n : ℕ) :
    (dickson 2 (s ^ 2) n).eval (s * t) = s ^ n * (Chebyshev.S R n).eval t := by
  rw [← mul_one (s ^ 2), dickson_sq_mul_eval_mul, dickson_two_one_eq_chebyshev_S]

/-- **The generating function of the Dickson values**:
`(∑ₙ (dickson 2 a n).eval t * Xⁿ) * (1 - t X + a X²) = 1` in `R⟦X⟧`.

This identifies the Eichler–Selberg weights with the Dickson values in any commutative ring, with
no inverse taken. Over a field, `PowerSeries.eq_inv_iff_mul_eq_one`
turns it into `PowerSeries.mk (fun n ↦ (dickson 2 a n).eval t) = (1 - C t * X + C a * X ^ 2)⁻¹`. -/
theorem mk_dickson_two_eval_mul_one_sub_add_eq_one (t a : R) :
    (PowerSeries.mk fun n ↦ (dickson 2 a n).eval t) *
      (1 - PowerSeries.C t * PowerSeries.X + PowerSeries.C a * PowerSeries.X ^ 2) = 1 := by
  simp only [mul_comm (PowerSeries.mk _), add_mul, sub_mul, one_mul, sq, mul_assoc]
  -- compare coefficients; at `X ^ (n + 2)` this is the recurrence `dickson_add_two`
  ext (_ | _ | n) <;> norm_num

end Polynomial
