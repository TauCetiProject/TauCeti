/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Sums of `x ^ a * (1 - x) ^ b` over a finite field

Let `K` be a finite field with `q` elements. Mathlib's `FiniteField.sum_pow_lt_card_sub_one`
says that `∑ x, x ^ i = 0` for `i < q - 1`. Expanding `(1 - x) ^ b` by the binomial theorem
reduces the sum of `x ^ a * (1 - x) ^ b` over `K` to such power sums, so it vanishes when
`a + b < q - 1`.

This is the finite-field input in the classical computation of Jacobi sums of power residue
characters modulo a prime: reducing `χ` and `φ` modulo the prime turns them into `x ↦ x ^ a`
and `x ↦ x ^ b`, so the Jacobi sum `J(χ, φ)` reduces to the sum above.

## Main results

* `TauCeti.FiniteField.sum_pow_mul_one_sub_pow_eq_zero`: `∑ x, x ^ a * (1 - x) ^ b = 0` when
  `a + b < q - 1`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §3,
  proof of Proposition 8.3.4.
-/

public section

open Finset

namespace TauCeti.FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- **A beta-type sum over a finite field.** If `a + b < q - 1`, where `q` is the number of
elements of the finite field `K`, then `∑ x, x ^ a * (1 - x) ^ b = 0`. -/
theorem sum_pow_mul_one_sub_pow_eq_zero {a b : ℕ} (h : a + b < Fintype.card K - 1) :
    ∑ x : K, x ^ a * (1 - x) ^ b = 0 := by
  simp_rw [← neg_add_eq_sub, add_pow, one_pow, mul_one, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun m hm ↦ ?_
  have hm : a + m < Fintype.card K - 1 := by
    rw [mem_range] at hm
    omega
  calc ∑ x : K, x ^ a * ((-x) ^ m * b.choose m)
      = ((-1) ^ m * b.choose m) * ∑ x : K, x ^ (a + m) := by
        rw [mul_sum]
        exact sum_congr rfl fun x _ ↦ by rw [neg_pow, pow_add]; ring
    _ = 0 := by rw [_root_.FiniteField.sum_pow_lt_card_sub_one K _ hm, mul_zero]

end TauCeti.FiniteField
