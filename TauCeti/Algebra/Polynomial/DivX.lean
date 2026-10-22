/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Iterated division by `X`

`Polynomial.divX p` drops the constant coefficient of `p` and lowers the remaining degrees by
one. Its `m`-th iterate `divX^[m] p` drops the `m` lowest coefficients and lowers the remaining
degrees by `m`, so that `(divX^[m] p).coeff n = p.coeff (n + m)`. This file records how the
iterate interacts with sums, scalars, multiplication by powers of `X` and reflection.

In terms of Laurent polynomials, `divX^[m] (Xᵐ * p)` is `p`, while the reflection
`reflect m q = Xᵐ q(X⁻¹)` of a polynomial `q` of degree at most `m` keeps only its constant
term `q(0)` under `divX^[m]`. These identities split a Laurent polynomial, written with
denominator `Xᵐ`, into its parts of positive and of nonpositive degree.
-/

public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The `m`-th iterate of `divX` lowers the indices of the coefficients by `m`. -/
@[simp]
theorem coeff_iterate_divX (m : ℕ) (p : R[X]) (n : ℕ) :
    (divX^[m] p).coeff n = p.coeff (n + m) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', coeff_divX, ih, add_right_comm, add_assoc]

/-- The iterates of `divX` are additive. -/
@[simp]
theorem iterate_divX_add (m : ℕ) (p q : R[X]) :
    divX^[m] (p + q) = divX^[m] p + divX^[m] q := by
  ext n
  simp

/-- The iterates of `divX` commute with scalar multiplication. -/
@[simp]
theorem iterate_divX_smul {S : Type*} [SMulZeroClass S R] (m : ℕ) (s : S) (p : R[X]) :
    divX^[m] (s • p) = s • divX^[m] p := by
  ext n
  simp

/-- After multiplication by `Xⁿ`, the `m`-th iterate of `divX` lowers the degrees by `m - n`, or
raises them by `n - m`. -/
theorem iterate_divX_X_pow_mul (m n : ℕ) (p : R[X]) :
    divX^[m] (X ^ n * p) = if m ≤ n then X ^ (n - m) * p else divX^[m - n] p := by
  ext k
  split_ifs with h
  · rw [coeff_iterate_divX, coeff_X_pow_mul', coeff_X_pow_mul']
    split_ifs <;> grind
  · rw [coeff_iterate_divX, coeff_iterate_divX, coeff_X_pow_mul']
    split_ifs <;> grind

/-- The `m`-th iterate of `divX` kills a polynomial of degree less than `m`. -/
theorem iterate_divX_eq_zero_of_natDegree_lt {m : ℕ} {p : R[X]} (h : p.natDegree < m) :
    divX^[m] p = 0 := by
  ext n
  rw [coeff_iterate_divX, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The `m`-th iterate of `divX` keeps only the constant coefficient of a polynomial of degree at
most `m` from its reflection `Xᵐ q(X⁻¹)`. -/
theorem iterate_divX_reflect {m : ℕ} {q : R[X]} (hq : q.natDegree ≤ m) :
    divX^[m] (reflect m q) = C (q.coeff 0) := by
  ext n
  rw [coeff_iterate_divX, coeff_reflect, coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [revAt_le]
  · rw [revAt_eq_self_of_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
    split_ifs <;> first | omega | rfl

end Semiring

/-- The iterates of `divX` commute with subtraction. -/
@[simp]
theorem iterate_divX_sub [Ring R] (m : ℕ) (p q : R[X]) :
    divX^[m] (p - q) = divX^[m] p - divX^[m] q := by
  ext n
  simp

end Polynomial
