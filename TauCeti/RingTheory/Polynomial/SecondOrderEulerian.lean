/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

import TauCeti.Algebra.Polynomial.Derivative

/-!
# Second-order Eulerian polynomials

The second-order Eulerian polynomial sequence `b_k = TauCeti.secondOrderEulerianPolynomial k` in
`ℤ[X]` is defined by `b₀(X) = 1` and the differential recurrence
`b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)` (Gessel–Stanley 1978, DLMF 8.11.8–8.11.9).
With this normalization `b₀ = 1`, `b₁ = X`, `b₂ = X + 2 X²`, `b₃ = X + 8 X² + 6 X³`, and
`b₄ = X + 22 X² + 58 X³ + 24 X⁴`: for `k ≥ 1`, the coefficient `[X^{m+1}] b_k` is the
second-order Eulerian number `⟪k, m⟫`, and `b_k(X) / (1 - X)^{2k + 1}` is the generating function
of the Stirling numbers of the second kind `S(m + k, m)`.

This sequence is distinct from the first-order Eulerian polynomials `TauCeti.eulerianPolynomial`
in `TauCeti/RingTheory/Polynomial/Eulerian.lean`, which satisfy a different recurrence and
normalization (`A₀ = A₁ = 1`, `A_k(1) = k!`, whereas `b_k(1) = (2k - 1)‼`).

## Main definitions

* `TauCeti.secondOrderEulerianPolynomial` — the polynomial sequence `b_k ∈ ℤ[X]`.

## Main results

* `TauCeti.secondOrderEulerianPolynomial_zero`, `TauCeti.secondOrderEulerianPolynomial_succ`:
  base case and defining differential recurrence (DLMF 8.11.8).
* `TauCeti.secondOrderEulerianPolynomial_one`, `TauCeti.secondOrderEulerianPolynomial_two`,
  `TauCeti.secondOrderEulerianPolynomial_three`, `TauCeti.secondOrderEulerianPolynomial_four`:
  the explicit polynomials of DLMF 8.11.9.
* `TauCeti.coeff_secondOrderEulerianPolynomial_succ_succ`: the second-order Eulerian coefficient
  recurrence `[X^{i+1}] b_{k+1} = (i + 1) [X^{i+1}] b_k + (2k + 1 - i) [X^i] b_k`.
* `TauCeti.natDegree_secondOrderEulerianPolynomial`,
  `TauCeti.leadingCoeff_secondOrderEulerianPolynomial`,
  `TauCeti.eval_one_secondOrderEulerianPolynomial`,
  `TauCeti.aeval_one_secondOrderEulerianPolynomial`: degree `k`, leading coefficient `k!`, and
  value `(2k - 1)‼` at `1`.
* `TauCeti.coeff_secondOrderEulerianPolynomial_nonneg`,
  `TauCeti.coeff_secondOrderEulerianPolynomial_pos`,
  `TauCeti.aeval_secondOrderEulerianPolynomial_nonneg`,
  `TauCeti.aeval_secondOrderEulerianPolynomial_pos`: nonnegativity and positivity of coefficients
  and evaluations over ordered commutative rings.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(ii)](https://dlmf.nist.gov/8.11#ii),
  Eqs. 8.11.8–8.11.9.
* I. Gessel and R. P. Stanley, *Stirling polynomials*, J. Combin. Theory Ser. A **24** (1978),
  24–33.
-/

public section

noncomputable section

open Polynomial
open scoped Nat

namespace TauCeti

/-- The second-order Eulerian polynomial sequence `b_k ∈ ℤ[X]` (Gessel–Stanley 1978;
DLMF 8.11.8–8.11.9): `b₀(X) = 1` and
`b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)`.
For `k ≥ 1`, the coefficient of `X^{m+1}` is the second-order Eulerian number `⟪k, m⟫`. -/
def secondOrderEulerianPolynomial : ℕ → ℤ[X]
  | 0 => 1
  | k + 1 =>
      X * (1 - X) * (secondOrderEulerianPolynomial k).derivative +
        C (2 * (k : ℤ) + 1) * X * secondOrderEulerianPolynomial k

/-- DLMF 8.11.9: `b₀(X) = 1`. -/
@[simp]
theorem secondOrderEulerianPolynomial_zero : secondOrderEulerianPolynomial 0 = 1 :=
  (rfl)

/-- DLMF 8.11.8: `b_{k+1}(X) = X (1 - X) b_k'(X) + (2k + 1) X b_k(X)`. -/
@[simp]
theorem secondOrderEulerianPolynomial_succ (k : ℕ) :
    secondOrderEulerianPolynomial (k + 1) =
      X * (1 - X) * (secondOrderEulerianPolynomial k).derivative +
        C (2 * (k : ℤ) + 1) * X * secondOrderEulerianPolynomial k :=
  (rfl)

/-- DLMF 8.11.9: `b₁(X) = X`. -/
theorem secondOrderEulerianPolynomial_one : secondOrderEulerianPolynomial 1 = X := by
  simp [secondOrderEulerianPolynomial]

/-- DLMF 8.11.9: `b₂(X) = X + 2 X²`. -/
theorem secondOrderEulerianPolynomial_two :
    secondOrderEulerianPolynomial 2 = X + 2 * X ^ 2 := by
  rw [secondOrderEulerianPolynomial, secondOrderEulerianPolynomial_one]
  simp only [derivative_X, Nat.cast_one, map_add, map_mul, map_ofNat, map_one]
  ring

/-- DLMF 8.11.9: `b₃(X) = X + 8 X² + 6 X³`. -/
theorem secondOrderEulerianPolynomial_three :
    secondOrderEulerianPolynomial 3 = X + 8 * X ^ 2 + 6 * X ^ 3 := by
  rw [secondOrderEulerianPolynomial, secondOrderEulerianPolynomial_two]
  simp only [derivative_X, derivative_mul, derivative_ofNat, derivative_X_pow_succ, Nat.cast_one,
    Nat.cast_ofNat, map_add, map_mul, map_ofNat, map_one]
  ring

/-- DLMF 8.11.9: `b₄(X) = X + 22 X² + 58 X³ + 24 X⁴`. -/
theorem secondOrderEulerianPolynomial_four :
    secondOrderEulerianPolynomial 4 = X + 22 * X ^ 2 + 58 * X ^ 3 + 24 * X ^ 4 := by
  rw [secondOrderEulerianPolynomial, secondOrderEulerianPolynomial_three]
  simp only [derivative_X, derivative_mul, derivative_ofNat, derivative_X_pow_succ, Nat.cast_one,
    Nat.cast_ofNat, map_add, map_mul, map_ofNat, map_one]
  ring

/-- For `k ≥ 1`, `b_k` vanishes at `0`. -/
theorem eval_zero_secondOrderEulerianPolynomial_succ (k : ℕ) :
    (secondOrderEulerianPolynomial (k + 1)).eval 0 = 0 := by
  simp

/-- Evaluating `b_k` at `0` gives `1` for `k = 0` and `0` for `k ≥ 1`. -/
theorem eval_zero_secondOrderEulerianPolynomial (k : ℕ) :
    (secondOrderEulerianPolynomial k).eval 0 = if k = 0 then 1 else 0 := by
  cases k <;> simp

/-- Evaluating `b_k` at `1` gives the odd double factorial `(2k - 1)‼`. -/
@[simp]
theorem eval_one_secondOrderEulerianPolynomial (k : ℕ) :
    (secondOrderEulerianPolynomial k).eval 1 = ((2 * k - 1)‼ : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [secondOrderEulerianPolynomial_succ, eval_add, eval_mul, eval_X, eval_sub, eval_one,
      sub_self, mul_zero, zero_mul, zero_add, eval_C, mul_one, ih]
    cases k with
    | zero => simp
    | succ m =>
      have hsub : 2 * (m + 2) - 1 = (2 * (m + 1) - 1) + 2 := by omega
      have hodd : (2 * ((m + 1 : ℕ) : ℤ) + 1) = ((2 * (m + 1) + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [hsub, Nat.doubleFactorial_add_two, Nat.cast_mul, hodd]
      congr 2

/-- Over any commutative ring, `b_{k+1}(0) = 0`. -/
theorem aeval_zero_secondOrderEulerianPolynomial_succ {R : Type*} [CommRing R] (k : ℕ) :
    aeval (0 : R) (secondOrderEulerianPolynomial (k + 1)) = 0 := by
  simp

/-- Over any commutative ring, `b_k(1) = (2k - 1)‼`. -/
@[simp]
theorem aeval_one_secondOrderEulerianPolynomial {R : Type*} [CommRing R] (k : ℕ) :
    aeval (1 : R) (secondOrderEulerianPolynomial k) = ((2 * k - 1)‼ : R) := by
  simpa using aeval_algebraMap_apply_eq_algebraMap_eval (A := R) (1 : ℤ)
    (secondOrderEulerianPolynomial k)

/-- Second-order Eulerian recurrence on the coefficients of `b_k`:
`[X^{i+1}] b_{k+1} = (i + 1) [X^{i+1}] b_k + (2k + 1 - i) [X^i] b_k`. -/
theorem coeff_secondOrderEulerianPolynomial_succ_succ (k i : ℕ) :
    (secondOrderEulerianPolynomial (k + 1)).coeff (i + 1) =
      (i + 1 : ℤ) * (secondOrderEulerianPolynomial k).coeff (i + 1) +
        (2 * (k : ℤ) + 1 - i) * (secondOrderEulerianPolynomial k).coeff i := by
  have hrew : secondOrderEulerianPolynomial (k + 1) =
      X * (secondOrderEulerianPolynomial k).derivative +
        X * (C (2 * (k : ℤ) + 1) * secondOrderEulerianPolynomial k -
          X * (secondOrderEulerianPolynomial k).derivative) := by
    rw [secondOrderEulerianPolynomial_succ]
    ring
  rw [hrew, coeff_add, coeff_X_mul_derivative, coeff_X_mul, coeff_sub, coeff_C_mul,
    coeff_X_mul_derivative]
  push_cast
  ring

/-- All coefficients of `b_k` strictly above degree `k` vanish. -/
theorem coeff_secondOrderEulerianPolynomial_eq_zero_of_lt {k j : ℕ} (hkj : k < j) :
    (secondOrderEulerianPolynomial k).coeff j = 0 := by
  induction k generalizing j with
  | zero =>
    rw [secondOrderEulerianPolynomial_zero, coeff_one]
    simp [hkj.ne']
  | succ k ih =>
    cases j with
    | zero => omega
    | succ i =>
      rw [coeff_secondOrderEulerianPolynomial_succ_succ, ih (by omega), ih (by omega)]
      ring

/-- The degree-`k` coefficient of `b_k` is `k!`. -/
@[simp]
theorem coeff_secondOrderEulerianPolynomial_self (k : ℕ) :
    (secondOrderEulerianPolynomial k).coeff k = (k ! : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [coeff_secondOrderEulerianPolynomial_succ_succ,
      coeff_secondOrderEulerianPolynomial_eq_zero_of_lt (Nat.lt_succ_self k), ih,
      Nat.factorial_succ]
    push_cast
    ring

/-- `b_k` has exact degree `k`. -/
@[simp]
theorem natDegree_secondOrderEulerianPolynomial (k : ℕ) :
    (secondOrderEulerianPolynomial k).natDegree = k := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun j hj =>
    coeff_secondOrderEulerianPolynomial_eq_zero_of_lt hj) ?_
  rw [coeff_secondOrderEulerianPolynomial_self]
  exact_mod_cast Nat.factorial_ne_zero k

/-- The leading coefficient of `b_k` is `k!`. -/
@[simp]
theorem leadingCoeff_secondOrderEulerianPolynomial (k : ℕ) :
    (secondOrderEulerianPolynomial k).leadingCoeff = (k ! : ℤ) := by
  rw [leadingCoeff, natDegree_secondOrderEulerianPolynomial,
    coeff_secondOrderEulerianPolynomial_self]

/-- Every coefficient of `b_k` is nonnegative. -/
theorem coeff_secondOrderEulerianPolynomial_nonneg (k j : ℕ) :
    0 ≤ (secondOrderEulerianPolynomial k).coeff j := by
  induction k generalizing j with
  | zero =>
    rw [secondOrderEulerianPolynomial_zero, coeff_one]
    split_ifs <;> norm_num
  | succ k ih =>
    cases j with
    | zero => simp [coeff_zero_eq_eval_zero]
    | succ i =>
      rcases lt_or_ge k i with hki | hik
      · rw [coeff_secondOrderEulerianPolynomial_eq_zero_of_lt (Nat.succ_lt_succ hki)]
      · rw [coeff_secondOrderEulerianPolynomial_succ_succ]
        refine add_nonneg (mul_nonneg (by positivity) (ih (i + 1)))
          (mul_nonneg ?_ (ih i))
        omega

/-- For `1 ≤ j ≤ k`, the `j`-th coefficient of `b_k` is strictly positive. -/
theorem coeff_secondOrderEulerianPolynomial_pos {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    0 < (secondOrderEulerianPolynomial k).coeff j := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => omega
    | succ i =>
      rw [coeff_secondOrderEulerianPolynomial_succ_succ]
      rcases eq_or_lt_of_le hjk with heq | hlt
      · obtain rfl : i = k := by omega
        rw [coeff_secondOrderEulerianPolynomial_eq_zero_of_lt (Nat.lt_succ_self i),
          coeff_secondOrderEulerianPolynomial_self]
        have hfac : (0 : ℤ) < (i ! : ℤ) := by exact_mod_cast Nat.factorial_pos i
        have hmul : (0 : ℤ) < 2 * (i : ℤ) + 1 - i := by omega
        linarith [mul_pos hmul hfac]
      · have hpos : 0 < (secondOrderEulerianPolynomial k).coeff (i + 1) :=
          ih (by omega) (by omega)
        have hnn : 0 ≤ (2 * (k : ℤ) + 1 - i) * (secondOrderEulerianPolynomial k).coeff i :=
          mul_nonneg (by omega) (coeff_secondOrderEulerianPolynomial_nonneg k i)
        have h1 : (0 : ℤ) < (i + 1 : ℤ) * (secondOrderEulerianPolynomial k).coeff (i + 1) :=
          mul_pos (by positivity) hpos
        linarith

/-- `b_k(x) ≥ 0` for `x ≥ 0` in any strict ordered commutative ring. -/
theorem aeval_secondOrderEulerianPolynomial_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ aeval x (secondOrderEulerianPolynomial k) := by
  rw [aeval_eq_sum_range]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Algebra.smul_def, eq_intCast]
  have hc : (0 : R) ≤ ((secondOrderEulerianPolynomial k).coeff i : R) := by
    exact_mod_cast coeff_secondOrderEulerianPolynomial_nonneg k i
  exact mul_nonneg hc (pow_nonneg hx i)

/-- `b_k(x) > 0` for `x > 0` in any strict ordered commutative ring. -/
theorem aeval_secondOrderEulerianPolynomial_pos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {x : R} (hx : 0 < x) (k : ℕ) :
    0 < aeval x (secondOrderEulerianPolynomial k) := by
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_secondOrderEulerianPolynomial k).le)]
  refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), ?_⟩
  · rw [Algebra.smul_def, eq_intCast]
    have hc : (0 : R) ≤ ((secondOrderEulerianPolynomial k).coeff i : R) := by
      exact_mod_cast coeff_secondOrderEulerianPolynomial_nonneg k i
    exact mul_nonneg hc (pow_nonneg hx.le i)
  · rw [Algebra.smul_def, eq_intCast, coeff_secondOrderEulerianPolynomial_self, Int.cast_natCast]
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) (pow_pos hx k)

end TauCeti

end
