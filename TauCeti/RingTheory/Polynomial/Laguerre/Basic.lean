/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The generalized Laguerre polynomials

This file defines the generalized Laguerre polynomial `Polynomial.laguerre α n`, written
`Lₙ^{(α)}`, over a commutative `ℚ`-algebra `R` with parameter `α : R`, by the explicit sum
(DLMF 18.5.12)

  `Lₙ^{(α)}(X) = ∑_{k ≤ n} (-1)ᵏ (α + k + 1)_{n-k} / ((n - k)! k!) Xᵏ`,

where `(a)ₘ = a (a + 1) ⋯ (a + m - 1)` is the rising factorial, Mathlib's `ascPochhammer R m`
evaluated at `a`. The factorials are inverted in `ℚ` and act on `R` through the algebra
structure, so no division in `R` is needed and `ℝ`, `ℂ` and polynomial rings over `ℚ` are all
instances. The parameter is a ring element rather than a fixed constant because the derivative
of `Lₙ₊₁^{(α)}` is `-Lₙ^{(α+1)}`.

We record the coefficients, the degree and leading coefficient (`(-1)ⁿ / n!`, DLMF Table 18.3.1),
the first two polynomials, and the value at the origin (DLMF 18.6.1). The exact degree is the
hypothesis under which polynomial completeness arguments apply to the Laguerre family and its
orthogonality measure `x^α e^{-x} dx`.

## Main declarations

* `Polynomial.laguerre`: the generalized Laguerre polynomial `Lₙ^{(α)}`.
* `Polynomial.coeff_laguerre`: the coefficient of `Xᵏ`.
* `Polynomial.degree_laguerre`, `Polynomial.natDegree_laguerre`: `Lₙ^{(α)}` has degree `n` over
  any nontrivial `ℚ`-algebra, for every value of the parameter.
* `Polynomial.leadingCoeff_laguerre`: the leading coefficient is `(-1)ⁿ / n!`.
* `Polynomial.eval_zero_laguerre`: `Lₙ^{(α)}(0) = (α + 1)ₙ / n!`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, Chapter 18:
  18.5.12 (the explicit sum), Table 18.3.1 (the leading coefficient) and 18.6.1 (the value at the
  origin).
* G. Szegő, *Orthogonal Polynomials*, Chapter V.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Laguerre polynomial `Lₙ^{(α)}` over a commutative `ℚ`-algebra, defined by the
explicit sum `∑_{k ≤ n} (-1)ᵏ (α + k + 1)_{n-k} / ((n - k)! k!) Xᵏ` (DLMF 18.5.12). The rising
factorial `(α + k + 1)_{n-k}` is `ascPochhammer R (n - k)` evaluated at `α + k + 1`, and the
factorials are inverted in `ℚ`. The simple Laguerre polynomial is `laguerre 0 n`. -/
noncomputable def laguerre (α : R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    ((-1 : R) ^ k * (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
      (ascPochhammer R (n - k)).smeval (α + k + 1))) • X ^ k

/-- The coefficient of `Xᵏ` in `Lₙ^{(α)}` is `(-1)ᵏ (α + k + 1)_{n-k} / ((n - k)! k!)` for
`k ≤ n`, and `0` otherwise. -/
theorem coeff_laguerre (α : R) (n k : ℕ) :
    (laguerre α n).coeff k =
      if k ≤ n then
        (-1 : R) ^ k * (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
          (ascPochhammer R (n - k)).smeval (α + k + 1))
      else 0 := by
  simp [laguerre, coeff_X_pow]

/-- The coefficient of `Xᵏ` in `Lₙ^{(α)}` for `k ≤ n`. -/
theorem coeff_laguerre_of_le (α : R) {n k : ℕ} (h : k ≤ n) :
    (laguerre α n).coeff k =
      (-1 : R) ^ k * (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
        (ascPochhammer R (n - k)).smeval (α + k + 1)) := by
  simp [coeff_laguerre, h]

/-- The coefficients of `Lₙ^{(α)}` vanish above degree `n`. -/
@[simp]
theorem coeff_laguerre_of_lt (α : R) {n k : ℕ} (h : n < k) : (laguerre α n).coeff k = 0 := by
  simp [coeff_laguerre, h.not_ge]

theorem natDegree_laguerre_le (α : R) (n : ℕ) : (laguerre α n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hk => coeff_laguerre_of_lt α (by exact_mod_cast hk)

theorem degree_laguerre_le (α : R) (n : ℕ) : (laguerre α n).degree ≤ n :=
  degree_le_of_natDegree_le (natDegree_laguerre_le α n)

/-- The coefficient of `Xⁿ` in `Lₙ^{(α)}` is `(-1)ⁿ / n!`, independently of the parameter. -/
@[simp]
theorem coeff_laguerre_self (α : R) (n : ℕ) :
    (laguerre α n).coeff n = algebraMap ℚ R ((-1) ^ n / n.factorial) := by
  rw [coeff_laguerre_of_le α le_rfl, Nat.sub_self, ascPochhammer_zero, ← C_1, smeval_C,
    Algebra.smul_def, Algebra.smul_def]
  simp [div_eq_mul_inv, mul_comm]

/-- Over a nontrivial `ℚ`-algebra the coefficient `(-1)ⁿ / n!` of `Xⁿ` in `Lₙ^{(α)}` is nonzero. -/
theorem coeff_laguerre_self_ne_zero [Nontrivial R] (α : R) (n : ℕ) :
    (laguerre α n).coeff n ≠ 0 := by
  rw [coeff_laguerre_self, map_ne_zero_iff _ (algebraMap ℚ R).injective]
  exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (by positivity)

/-- `Lₙ^{(α)}` has natural degree `n` for every value of the parameter `α`. -/
@[simp]
theorem natDegree_laguerre [Nontrivial R] (α : R) (n : ℕ) : (laguerre α n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_laguerre_le α n) (coeff_laguerre_self_ne_zero α n)

/-- `Lₙ^{(α)}` has degree `n` for every value of the parameter `α`, including the negative
integers. -/
@[simp]
theorem degree_laguerre [Nontrivial R] (α : R) (n : ℕ) : (laguerre α n).degree = n :=
  degree_eq_of_le_of_coeff_ne_zero (degree_laguerre_le α n) (coeff_laguerre_self_ne_zero α n)

/-- The leading coefficient of `Lₙ^{(α)}` is `(-1)ⁿ / n!` (DLMF Table 18.3.1). -/
@[simp]
theorem leadingCoeff_laguerre (α : R) (n : ℕ) :
    (laguerre α n).leadingCoeff = algebraMap ℚ R ((-1) ^ n / n.factorial) := by
  nontriviality R
  rw [leadingCoeff, natDegree_laguerre, coeff_laguerre_self]

/-- `L₀^{(α)} = 1`. -/
@[simp]
theorem laguerre_zero (α : R) : laguerre α 0 = 1 := by
  simp [laguerre]

/-- `L₁^{(α)} = α + 1 - X`. -/
@[simp]
theorem laguerre_one (α : R) : laguerre α 1 = C (α + 1) - X := by
  simp [laguerre, Finset.sum_range_succ, smul_eq_C_mul, sub_eq_add_neg]

/-- The value of `Lₙ^{(α)}` at the origin is `(α + 1)ₙ / n!` (DLMF 18.6.1). -/
theorem eval_zero_laguerre (α : R) (n : ℕ) :
    (laguerre α n).eval 0 = ((1 : ℚ) / n.factorial) • (ascPochhammer R n).smeval (α + 1) := by
  simp [← coeff_zero_eq_eval_zero, coeff_laguerre_of_le α (Nat.zero_le n)]

/-- The simple Laguerre polynomials take the value `1` at the origin: `Lₙ^{(0)}(0) = 1`. -/
@[simp]
theorem eval_zero_laguerre_zero_left (n : ℕ) : (laguerre (0 : R) n).eval 0 = 1 := by
  -- `Lₙ^{(0)}(0) = (1 / n!) • (1)ₙ = (1 / n!) • n!`, and `1 / n! * n! = 1` in `ℚ`
  have h : (1 : ℚ) / n.factorial * n.factorial = 1 :=
    div_mul_cancel₀ 1 (Nat.cast_ne_zero.2 n.factorial_ne_zero)
  rw [eval_zero_laguerre, zero_add, ← eval_eq_smeval, ascPochhammer_eval_one]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ R), ← map_mul, h, map_one]

end Polynomial
