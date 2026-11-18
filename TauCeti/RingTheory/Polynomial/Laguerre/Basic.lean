/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The generalized Laguerre polynomials

This file defines the generalized Laguerre polynomial `Lₙ^{(α)}` over a `ℚ`-algebra `R`, with
parameter `α : R`, by the explicit sum (DLMF 18.5.12)

`Lₙ^{(α)}(X) = ∑_{k ≤ n} (-1)^k (α + k + 1)_{n-k} / ((n-k)! k!) X^k`,

where `(a)_m` is the rising factorial, evaluated as `(ascPochhammer R m).smeval a`. Since `R` need
not have division, the factorial coefficients `1 / ((n-k)! k!)` are rational numbers acting on `R`
through the `ℚ`-algebra structure.

The Laguerre polynomials are the orthogonal polynomials of the Gamma weight `x^α e^{-x}` on
`(0, ∞)`; the parameter is a variable of the definition, rather than fixed at `0`, because the
derivative of `Lₙ₊₁^{(α)}` is `-Lₙ^{(α+1)}` (DLMF 18.9.23). This file develops the
coefficients: the explicit coefficient of every `X^k`, the leading coefficient `(-1)^n / n!`, and
hence that `Lₙ^{(α)}` has degree exactly `n` for every value of the parameter (no nondegeneracy
condition on `α` is needed, in contrast with the Jacobi family), together with the value
`(α + 1)ₙ / n!` at the origin.

## Main definitions

* `Polynomial.laguerre α n`: the generalized Laguerre polynomial `Lₙ^{(α)}`.

## Main statements

* `Polynomial.coeff_laguerre`: the coefficient of `X^k` in `Lₙ^{(α)}`.
* `Polynomial.leadingCoeff_laguerre`: the leading coefficient is `(-1)^n / n!`.
* `Polynomial.degree_laguerre`, `Polynomial.natDegree_laguerre`: `Lₙ^{(α)}` has degree `n`.
* `Polynomial.eval_zero_laguerre`: `Lₙ^{(α)}(0) = (α + 1)ₙ / n!`, and
  `Polynomial.eval_zero_laguerre_zero`: the simple Laguerre polynomials take the value `1` at `0`.
* `Polynomial.laguerre_zero`, `Polynomial.laguerre_one`: `L₀^{(α)} = 1` and
  `L₁^{(α)} = α + 1 - X`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.12 (the
  explicit sum), Table 18.3.1 (the leading coefficient) and 18.6.1 (the value at the origin).
* G. Szegő, *Orthogonal Polynomials*, Ch. V.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Laguerre polynomial `Lₙ^{(α)}` over a `ℚ`-algebra,
`∑ k ≤ n, (-1)^k (α + k + 1)_{n-k} / ((n-k)! k!) • X^k` (DLMF 18.5.12). The rising factorial
`(α + k + 1)_{n-k}` is `(ascPochhammer R (n - k)).smeval (α + k + 1)`, and the rational factorial
coefficients are `ℚ`-scalars acting on it. -/
noncomputable def laguerre (α : R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    ((-1 : R) ^ k * (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
      (ascPochhammer R (n - k)).smeval (α + k + 1))) • X ^ k

/-- The coefficient of `X^k` in `Lₙ^{(α)}` is `(-1)^k (α + k + 1)_{n-k} / ((n-k)! k!)` for
`k ≤ n`, and `0` for `n < k`. -/
theorem coeff_laguerre (α : R) (n k : ℕ) :
    (laguerre α n).coeff k =
      if k ≤ n then
        (-1 : R) ^ k * (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
          (ascPochhammer R (n - k)).smeval (α + k + 1))
      else 0 := by
  simp [laguerre]

theorem coeff_laguerre_of_lt (α : R) {n k : ℕ} (h : n < k) : (laguerre α n).coeff k = 0 := by
  simp [coeff_laguerre, h.not_ge]

/-- The coefficient of `X^n` in `Lₙ^{(α)}` is `(-1)^n / n!`. -/
@[simp]
theorem coeff_laguerre_self (α : R) (n : ℕ) :
    (laguerre α n).coeff n = algebraMap ℚ R ((-1) ^ n / n.factorial) := by
  simp [coeff_laguerre, Algebra.smul_def, div_eq_mul_inv]

/-- The value of `Lₙ^{(α)}` at the origin is `(α + 1)ₙ / n!` (DLMF 18.6.1). -/
theorem eval_zero_laguerre (α : R) (n : ℕ) :
    (laguerre α n).eval 0 = ((1 : ℚ) / n.factorial) • (ascPochhammer R n).smeval (α + 1) := by
  simp [← coeff_zero_eq_eval_zero, coeff_laguerre]

/-- The simple Laguerre polynomial `Lₙ = Lₙ^{(0)}` takes the value `1` at the origin. -/
@[simp]
theorem eval_zero_laguerre_zero (n : ℕ) : (laguerre (0 : R) n).eval 0 = 1 := by
  rw [eval_zero_laguerre, zero_add, ← eval_eq_smeval, ascPochhammer_eval_one]
  -- The remaining goal `(1 / n!) • n! = 1` is computed in `ℚ`.
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ R), ← map_mul, one_div,
    inv_mul_cancel₀ (by positivity), map_one]

theorem natDegree_laguerre_le (α : R) (n : ℕ) : (laguerre α n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hk => coeff_laguerre_of_lt α (by exact_mod_cast hk)

theorem degree_laguerre_le (α : R) (n : ℕ) : (laguerre α n).degree ≤ n :=
  degree_le_of_natDegree_le (natDegree_laguerre_le α n)

theorem coeff_laguerre_self_ne_zero [Nontrivial R] (α : R) (n : ℕ) :
    (laguerre α n).coeff n ≠ 0 := by
  rw [coeff_laguerre_self, map_ne_zero_iff _ (algebraMap ℚ R).injective]
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (Nat.cast_ne_zero.2 n.factorial_ne_zero)

/-- `Lₙ^{(α)}` has degree exactly `n`, for every value of the parameter `α`. -/
@[simp]
theorem degree_laguerre [Nontrivial R] (α : R) (n : ℕ) : (laguerre α n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_laguerre_le α n) (coeff_laguerre_self_ne_zero α n)

@[simp]
theorem natDegree_laguerre [Nontrivial R] (α : R) (n : ℕ) : (laguerre α n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_laguerre_le α n)
    (coeff_laguerre_self_ne_zero α n)

/-- The leading coefficient of `Lₙ^{(α)}` is `(-1)^n / n!` (DLMF Table 18.3.1). -/
@[simp]
theorem leadingCoeff_laguerre (α : R) (n : ℕ) :
    (laguerre α n).leadingCoeff = algebraMap ℚ R ((-1) ^ n / n.factorial) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  · rw [leadingCoeff, natDegree_laguerre, coeff_laguerre_self]

@[simp]
theorem laguerre_zero (α : R) : laguerre α 0 = 1 := by
  simp [laguerre]

/-- `L₁^{(α)} = α + 1 - X`. -/
@[simp]
theorem laguerre_one (α : R) : laguerre α 1 = C (α + 1) - X := by
  simp [laguerre, Finset.sum_range_succ, smul_eq_C_mul, sub_eq_add_neg]

end Polynomial
