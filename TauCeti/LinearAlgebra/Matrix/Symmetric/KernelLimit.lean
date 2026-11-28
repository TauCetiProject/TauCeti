/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Analysis.SpecialFunctions.QPochhammer

/-!
# Normalization of the binary symmetric kernel limit

`TauCeti.hasSum_symmetricKernelLimit` shows that the proposed limiting masses for the nullity of
uniform symmetric matrices over the two-element field sum to one. The finite-size counts are
given by `Matrix.natCard_isSymm_rank_eq_prod` in `TauCeti.LinearAlgebra.Matrix.Symmetric.RankCount`.
The normalization uses Euler's series expansion
`TauCeti.hasSum_tprod_one_sub_mul_pow` and the complementary odd product identity
`TauCeti.tprod_one_add_pow_mul_tprod_one_sub_pow_odd`.

## References

* P. Koymans and C. Pagano, *On Stevenhagen's conjecture*, Theorem 7.13, arXiv:2201.13424v1.
* B. Poonen and E. Rains, *Random maximal isotropic subspaces and Selmer groups*,
  Proposition 2.6(e)–(f), arXiv:1009.0287v2.
-/

public section

namespace TauCeti

open Finset

/-- The odd Euler product divided by `∏_{i=1}^n (2^i - 1)` gives a sequence with sum one,
including the empty denominator product at `n = 0` (Koymans–Pagano, Theorem 7.13). -/
theorem hasSum_symmetricKernelLimit :
    HasSum (fun n : ℕ ↦ (∏' j : ℕ, (1 - (2 : ℝ)⁻¹ ^ (2 * j + 1))) /
      ∏ i ∈ range n, ((2 : ℝ) ^ (i + 1) - 1)) 1 := by
  let q : ℝ := (2 : ℝ)⁻¹
  have hq : ‖q‖ < 1 := by norm_num [q]
  have hterm (n : ℕ) :
      (-1 : ℝ) ^ n * q ^ n.choose 2 * (-q) ^ n / qPochhammer q q n =
        (∏ i ∈ range n, ((2 : ℝ) ^ (i + 1) - 1))⁻¹ := by
    have hq₀ : q ≠ 0 := by norm_num [q]
    have hsum : ∑ i ∈ range n, (i + 1) = n.choose 2 + n := by
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
      rw [← hchoose, Nat.choose_two_right, ← sum_range_id (n + 1), sum_range_succ', add_zero]
    have hden : qPochhammer q q n =
        (∏ i ∈ range n, ((2 : ℝ) ^ (i + 1) - 1)) * q ^ (n.choose 2 + n) := by
      rw [qPochhammer_self, ← hsum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ ↦ ?_
      have hpow : (2 : ℝ) ^ (i + 1) ≠ 0 := by positivity
      simp only [q, inv_pow, sub_mul, one_mul, mul_inv_cancel₀ hpow]
    have hsign : (-1 : ℝ) ^ n * q ^ n.choose 2 * (-q) ^ n = q ^ (n.choose 2 + n) := by
      rw [mul_comm ((-1 : ℝ) ^ n), mul_assoc, ← mul_pow]
      simp only [neg_mul, one_mul, neg_neg, pow_add]
    rw [hsign, hden, div_mul_cancel_right₀ (pow_ne_zero _ hq₀)]
  have hprod : (∏' j : ℕ, (1 - (-q) * q ^ j)) = ∏' j : ℕ, (1 + q ^ (j + 1)) :=
    tprod_congr fun j ↦ by rw [neg_mul, sub_neg_eq_add, pow_succ']
  have hseries := (hasSum_tprod_one_sub_mul_pow hq (-q)).congr_fun fun n ↦ (hterm n).symm
  have h := hseries.mul_left (∏' j : ℕ, (1 - q ^ (2 * j + 1)))
  rw [hprod, mul_comm, tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq] at h
  simpa only [div_eq_mul_inv] using h

end TauCeti
