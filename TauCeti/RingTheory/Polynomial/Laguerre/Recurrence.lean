/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Laguerre.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import TauCeti.Data.Nat.Factorial.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Derivative and recurrences of the generalized Laguerre polynomials

For the generalized Laguerre polynomials `Lₙ^{(α)} = Polynomial.laguerre α n` over a commutative
`ℚ`-algebra this file proves the classical identities that relate neighbouring indices and
parameters:

* `Polynomial.derivative_laguerre`: `(Lₙ₊₁^{(α)})' = -Lₙ^{(α+1)}` (DLMF 18.9.23), the identity
  that moves the parameter;
* `Polynomial.laguerre_add_one_sub`: `Lₙ₊₁^{(α)} = Lₙ₊₁^{(α+1)} - Lₙ^{(α+1)}` (DLMF 18.9.13);
* `Polynomial.X_mul_laguerre_add_one`:
  `X Lₙ^{(α+1)} = (n + α + 1) Lₙ^{(α)} - (n + 1) Lₙ₊₁^{(α)}` (DLMF 18.9.14);
* `Polynomial.laguerre_succ_succ`, the three-term recurrence (DLMF 18.9.1 with Table 18.9.1)
  `(n + 2) Lₙ₊₂^{(α)} = (2n + α + 3 - X) Lₙ₊₁^{(α)} - (n + α + 1) Lₙ^{(α)}`.

The first three are proved by comparing coefficients; the three-term recurrence is a linear
combination of the other two. Every identity involving the index `n - 1` is stated at successor
indices, since the `n`-indexed forms are false at `n = 0` under truncated subtraction (for
instance `(L₀^{(α)})' = 0`, while `-L₀^{(α+1)} = -1`).

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, Chapter 18:
  18.9.1 with Table 18.9.1, 18.9.13, 18.9.14 and 18.9.23.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient of `Xᵏ` in `Lₙ^{(α)}` for `k ≤ n`, with the rational factor written through
`algebraMap` and the rising factorial through `eval`, the shape used by the coefficient
comparisons below. -/
private theorem coeff_laguerre_of_le_eq (α : R) {n k : ℕ} (h : k ≤ n) :
    (laguerre α n).coeff k =
      (-1 : R) ^ k * algebraMap ℚ R (1 / ((n - k).factorial * k.factorial)) *
        (ascPochhammer R (n - k)).eval (α + k + 1) := by
  rw [coeff_laguerre_of_le α h, Algebra.smul_def, eval_eq_smeval, mul_assoc]

/-- The derivative of a Laguerre polynomial raises the parameter and lowers the index:
`(Lₙ₊₁^{(α)})' = -Lₙ^{(α+1)}` (DLMF 18.9.23). It is stated at index `n + 1` because the
`n`-indexed form fails at `n = 0`. -/
@[simp]
theorem derivative_laguerre (α : R) (n : ℕ) :
    derivative (laguerre α (n + 1)) = -laguerre (α + 1) n := by
  ext k
  rw [coeff_derivative, coeff_neg]
  rcases le_or_gt k n with hk | hk
  · rw [coeff_laguerre_of_le_eq α (by omega : k + 1 ≤ n + 1), coeff_laguerre_of_le_eq _ hk,
      Nat.add_sub_add_right, Nat.one_div_factorial_mul_factorial_succ_right (n - k) k]
    simp only [map_mul, map_add, map_natCast, map_one]
    have hα : α + ((k + 1 : ℕ) : R) + 1 = α + 1 + k + 1 := by push_cast; ring
    rw [hα]
    ring
  · simp [coeff_laguerre_of_lt _ (by omega : n + 1 < k + 1), coeff_laguerre_of_lt _ hk]

/-- The contiguous relation in the parameter: `Lₙ₊₁^{(α)} = Lₙ₊₁^{(α+1)} - Lₙ^{(α+1)}`
(DLMF 18.9.13). -/
theorem laguerre_add_one_sub (α : R) (n : ℕ) :
    laguerre α (n + 1) = laguerre (α + 1) (n + 1) - laguerre (α + 1) n := by
  ext k
  rw [coeff_sub]
  rcases lt_trichotomy k (n + 1) with hk | rfl | hk
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
    rw [coeff_laguerre_of_le_eq α hk.le, coeff_laguerre_of_le_eq _ hk.le,
      coeff_laguerre_of_le_eq _ (Nat.le_add_left k m), (by omega : m + k + 1 - k = m + 1),
      Nat.add_sub_cancel, Nat.one_div_factorial_mul_factorial_succ_left m k]
    simp only [map_mul, map_add, map_natCast, map_one]
    -- `(a)ₘ₊₁ = a (a + 1)ₘ` and `(a + 1)ₘ₊₁ = (a + 1)ₘ (a + 1 + m)` for `a = α + k + 1`
    have e : (ascPochhammer R (m + 1)).eval (α + k + 1) =
        (α + k + 1) * (ascPochhammer R m).eval (α + 1 + k + 1) := by
      rw [ascPochhammer_succ_left]
      simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
      rw [show α + k + 1 + 1 = α + 1 + k + 1 by ring]
    rw [e, ascPochhammer_succ_eval]
    ring
  · simp
  · simp [coeff_laguerre_of_lt _ hk, coeff_laguerre_of_lt _ (by omega : n < k)]

/-- Multiplication by `X` lowers the parameter:
`X Lₙ^{(α+1)} = (n + α + 1) Lₙ^{(α)} - (n + 1) Lₙ₊₁^{(α)}` (DLMF 18.9.14). -/
theorem X_mul_laguerre_add_one (α : R) (n : ℕ) :
    X * laguerre (α + 1) n = C (n + α + 1) * laguerre α n - (n + 1) • laguerre α (n + 1) := by
  ext k
  rw [coeff_sub, coeff_C_mul, nsmul_eq_mul, ← C_eq_natCast, coeff_C_mul]
  rcases k with _ | j
  · rw [coeff_X_mul_zero, coeff_laguerre_of_le_eq α (Nat.zero_le n),
      coeff_laguerre_of_le_eq α (Nat.zero_le (n + 1)), Nat.sub_zero, Nat.sub_zero,
      ascPochhammer_succ_eval, Nat.one_div_factorial_mul_factorial_succ_left n 0]
    push_cast
    ring
  rw [coeff_X_mul]
  rcases lt_trichotomy j n with hj | rfl | hj
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + (j + 1) := ⟨n - (j + 1), by omega⟩
    rw [coeff_laguerre_of_le_eq _ hj.le, coeff_laguerre_of_le_eq α hj,
      coeff_laguerre_of_le_eq α (by omega : j + 1 ≤ m + (j + 1) + 1),
      (by omega : m + (j + 1) - j = m + 1), (by omega : m + (j + 1) + 1 - (j + 1) = m + 1),
      Nat.add_sub_cancel, Nat.one_div_factorial_mul_factorial_succ_right (m + 1) j,
      Nat.one_div_factorial_mul_factorial_succ_left m (j + 1)]
    simp only [map_mul, map_add, map_natCast, map_one]
    have ha : α + 1 + j + 1 = α + ((j + 1 : ℕ) : R) + 1 := by push_cast; ring
    rw [ha, ascPochhammer_succ_eval]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    ring
  · have hq : ((-1 : ℚ) ^ j / j.factorial) = -((j + 1) * ((-1) ^ (j + 1) / (j + 1).factorial)) := by
      rw [Nat.factorial_succ]; push_cast; field_simp; ring
    rw [coeff_laguerre_self, coeff_laguerre_of_lt α (Nat.lt_succ_self j), coeff_laguerre_self, hq]
    simp only [map_neg, map_mul, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
    ring
  · simp [coeff_laguerre_of_lt _ hj, coeff_laguerre_of_lt _ (by omega : n < j + 1),
      coeff_laguerre_of_lt _ (by omega : n + 1 < j + 1)]

/-- The three-term recurrence of the generalized Laguerre polynomials (DLMF 18.9.1 with
Table 18.9.1), at shifted indices:
`(n + 2) Lₙ₊₂^{(α)} = (2n + α + 3 - X) Lₙ₊₁^{(α)} - (n + α + 1) Lₙ^{(α)}`. -/
theorem laguerre_succ_succ (α : R) (n : ℕ) :
    (n + 2) • laguerre α (n + 2) =
      (C (2 * n + α + 3) - X) * laguerre α (n + 1) - C (n + α + 1) * laguerre α n := by
  have h₁ := X_mul_laguerre_add_one α (n + 1)
  have h₂ := X_mul_laguerre_add_one α n
  have h₃ := laguerre_add_one_sub α n
  rw [show n + 1 + 1 = n + 2 by ring] at h₁
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, map_add, map_mul,
    map_natCast, map_one, map_ofNat] at h₁ h₂ ⊢
  linear_combination h₁ + X * h₃ - h₂

end Polynomial
