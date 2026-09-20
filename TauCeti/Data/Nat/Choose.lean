/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary identities for binomial coefficients

This file records arithmetic identities involving natural-number binomial coefficients.

Besides two identities for the second binomial coefficient, it develops Vandermonde's convolution
`∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` in the shape taken by factorial moments of a law
supported on such a convolution: each summand is weighted by the falling factorial `(i)ₘ` of the
summation index. The weighted sum is again a single binomial coefficient,
`(A)ₘ * C(A + B - m, r - m)`, because `(i)ₘ` lowers both indices of `C(A, i)` at once.

## Main results

* `Nat.choose_two_add_mul_succ_div_two`: the sum of the second binomial coefficient and
  the triangular number is the corresponding square.
* `Nat.add_choose_two`: the second binomial coefficient of a sum, with its cross term.
* `Nat.descFactorial_mul_choose`: a falling factorial of the lower index lowers both indices,
  `(i)ₘ * C(A, i) = (A)ₘ * C(A - m, i - m)`.
* `Nat.add_choose_eq_sum_range`: Vandermonde's convolution, summed over a range.
* `Nat.sum_range_descFactorial_mul_choose_mul_choose`: Vandermonde's convolution weighted by a
  falling factorial of the summation index.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1 (the absorption identity) and Section 5.2 (Vandermonde's convolution).
-/

public section

open Finset

namespace Nat

/-- The sum of `N.choose 2` and the `N`th triangular number is `N ^ 2`. -/
theorem choose_two_add_mul_succ_div_two (N : ℕ) :
    N.choose 2 + N * (N + 1) / 2 = N * N := by
  rw [Nat.choose_two_right]
  apply Nat.mul_right_cancel (by norm_num : 0 < 2)
  rw [Nat.add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd,
    Nat.div_mul_cancel (Nat.even_mul_succ_self N).two_dvd]
  by_cases hN : N = 0
  · simp [hN]
  · rw [← Nat.mul_add]
    have hsum : N - 1 + (N + 1) = 2 * N := by omega
    rw [hsum]
    ring

/-- The second binomial coefficient of a sum: `C(m + n, 2) = C(m, 2) + C(n, 2) + mn`. -/
theorem add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (m + (n + 1)).choose 2 = (m + n).choose 1 + (m + n).choose 2 := by
        rw [← Nat.add_assoc]
        exact Nat.choose_succ_succ (m + n) 1
      have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
      ring

/-- **A falling factorial of the lower index lowers both indices of a binomial coefficient:**
`(i)ₘ * C(A, i) = (A)ₘ * C(A - m, i - m)` for `m ≤ i`.

Both sides count the pairs consisting of an `i`-element subset of an `A`-element set and an
ordered `m`-tuple of distinct elements of that subset. The hypothesis `m ≤ i` is needed: for
`i < m` the left-hand side vanishes while the right-hand side need not. -/
theorem descFactorial_mul_choose {m i : ℕ} (hmi : m ≤ i) (A : ℕ) :
    i.descFactorial m * A.choose i = A.descFactorial m * (A - m).choose (i - m) := by
  rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (i.choose m) (A.choose i), choose_mul hmi]

/-- **Vandermonde's convolution, summed over a range.** This is `Nat.add_choose_eq` with the
antidiagonal of `r` presented as `Finset.range (r + 1)`. -/
theorem add_choose_eq_sum_range (A B r : ℕ) :
    (A + B).choose r = ∑ i ∈ range (r + 1), A.choose i * B.choose (r - i) := by
  rw [Nat.add_choose_eq]
  simpa using Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => A.choose i * B.choose j) r

/-- **Vandermonde's convolution weighted by a falling factorial of the summation index.**

Weighting the `i`th summand of `∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` by `(i)ₘ` multiplies
the value by `(A)ₘ` and lowers both indices by `m`. The cases `m = 1` and `m = 2` are the first
two factorial moments of a hypergeometric law. -/
theorem sum_range_descFactorial_mul_choose_mul_choose {m r : ℕ} (hmr : m ≤ r) (A B : ℕ) :
    ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A + B - m).choose (r - m) := by
  -- Only the indices `m ≤ i` contribute, since `(i)ₘ` vanishes below `m`.
  have hsub : Ico m (r + 1) ⊆ range (r + 1) := fun i hi => mem_range.2 (mem_Ico.1 hi).2
  have hvanish : ∀ i ∈ range (r + 1), i ∉ Ico m (r + 1) →
      i.descFactorial m * (A.choose i * B.choose (r - i)) = 0 := by
    intro i hi hni
    simp only [mem_range] at hi
    simp only [mem_Ico, not_and, not_lt] at hni
    simp [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : i < m)]
  -- After shifting the index by `m`, the weight becomes the constant `(A)ₘ` and what is left
  -- is the unweighted convolution of `A - m` with `B`.
  have key : ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A - m + B).choose (r - m) := by
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_Ico_eq_sum_range,
      show r + 1 - m = r - m + 1 from by omega, Nat.add_choose_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hri : r - (m + i) = r - m - i := by omega
    rw [hri, ← Nat.mul_assoc, Nat.descFactorial_mul_choose (Nat.le_add_right m i) A,
      Nat.add_sub_cancel_left, Nat.mul_assoc]
  -- The two ways of subtracting `m` agree unless `A < m`, where `(A)ₘ` is zero anyway.
  rcases le_or_gt m A with hmA | hmA
  · rwa [show A + B - m = A - m + B from by omega]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmA] at key ⊢
    simpa using key

end Nat
