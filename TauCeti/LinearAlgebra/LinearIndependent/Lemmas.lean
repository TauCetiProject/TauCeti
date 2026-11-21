/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence from a family of separating linear forms

A family `v` is linearly independent when there are linear forms `f i` with `f i (v j) = 0` for
`i ≠ j` and `f i (v i) ≠ 0`, over a ring without zero divisors. This relaxes the normalization
`f i (v i) = 1` of Mathlib's `LinearIndependent.of_pairwise_dual_eq_zero_one`.

## Main results

* `LinearIndependent.of_pairwise_dual_eq_zero_ne_zero`: linear independence from linear forms
  vanishing off the diagonal and nonzero on it.
-/

public section

open Module

variable {ι R M : Type*} [Ring R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]

/-- If `v : ι → M` is a family of vectors and there exists a family of linear forms
`f : ι → Dual R M` such that `f i (v j)` is `0` for `i ≠ j` and nonzero for `i = j`, then `v` is
linearly independent. -/
theorem LinearIndependent.of_pairwise_dual_eq_zero_ne_zero (v : ι → M) (f : ι → Dual R M)
    (h₀ : Pairwise fun i j ↦ f i (v j) = 0) (h₁ : ∀ i, f i (v i) ≠ 0) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s g hrel i hi ↦ ?_
  have h := congr(f i $hrel)
  rw [map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji ↦ by simp [h₀ hji.symm])
    (fun hi' ↦ absurd hi hi'), map_smul, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_right (h₁ i)
