/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RootsOfUnity.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
# Partial fractions over roots of unity

For a primitive `n`-th root of unity `ζ` in a field and `y ^ n ≠ 1`, summing
`1 / (ζ ^ i * y - 1)` over `i < n` gives `n / (y ^ n - 1)`. Every denominator
in the sum is nonzero. This identity evaluates finite root averages of rational functions,
in particular those appearing in the Frobenius calculus for p-adic measures.

The identity holds for arbitrary orders and in every characteristic, without a
characteristic-zero or prime-order hypothesis.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Lemma 4.7, p. 137.
-/

public section

open Finset

variable {K : Type*} {n : ℕ}

namespace IsPrimitiveRoot

variable [Field K] {ζ y : K}

/-- The sum of the simple fractions at all translates by powers of a primitive root is
`n / (y ^ n - 1)`. No primality or characteristic-zero assumption is needed. -/
theorem sum_inv_pow_mul_sub_one (hζ : IsPrimitiveRoot ζ n) (hy : y ^ n ≠ 1) :
    ∑ i ∈ range n, (ζ ^ i * y - 1)⁻¹ = (n : K) / (y ^ n - 1) := by
  classical
  have hn : 0 < n := by
    by_contra h
    simp [Nat.eq_zero_of_not_pos h] at hy
  have hgeom (i : ℕ) :
      (ζ ^ i * y - 1)⁻¹ = (∑ k ∈ range n, (ζ ^ i * y) ^ k) / (y ^ n - 1) := by
    apply (eq_div_iff (sub_ne_zero.mpr hy)).mpr
    have hp : (ζ ^ i * y) ^ n = y ^ n := by
      simp [mul_pow, pow_right_comm ζ i n, hζ.pow_eq_one]
    have hden := TauCeti.mul_sub_one_ne_zero_of_pow_eq_one
      (by simp [pow_right_comm ζ i n, hζ.pow_eq_one] : (ζ ^ i) ^ n = 1) hy
    rw [← hp, ← geom_sum_mul]
    field_simp [hden]
  simp_rw [hgeom, ← sum_div]
  congr 1
  rw [sum_comm]
  calc
    ∑ k ∈ range n, ∑ i ∈ range n, (ζ ^ i * y) ^ k =
        ∑ k ∈ range n, (if n ∣ k then (n : K) else 0) * y ^ k := by
      apply sum_congr rfl
      intro k hk
      simp_rw [mul_pow, pow_right_comm ζ _ k]
      rw [← sum_mul, ← Fin.sum_univ_eq_sum_range, hζ.sum_pow_pow_eq]
    _ = n := by
      have hdiv (k : ℕ) (hk : k ∈ range n) : n ∣ k ↔ k = 0 :=
        Nat.dvd_iff_mod_eq_zero.trans (by rw [Nat.mod_eq_of_lt (mem_range.mp hk)])
      trans ∑ k ∈ range n, (if k = 0 then (n : K) else 0) * y ^ k
      · exact sum_congr rfl fun k hk ↦ by simp only [hdiv k hk]
      · simp [hn]

end IsPrimitiveRoot

-- The dyadic root gives the sum of two fractions, with no omitted factor of two.
example {y : ℚ} (hy : y ^ 2 ≠ 1) :
    (y - 1)⁻¹ + (-y - 1)⁻¹ = 2 / (y ^ 2 - 1) := by
  have hζ := IsPrimitiveRoot.neg_one_of_two_ne_zero (by norm_num : (2 : ℚ) ≠ 0)
  simpa [sum_range_succ] using hζ.sum_inv_pow_mul_sub_one hy

-- At an excluded pole, totalized inversion does not salvage the identity.
example : (∑ i ∈ range 2, ((-1 : ℚ) ^ i * 1 - 1)⁻¹) ≠ 2 / ((1 : ℚ) ^ 2 - 1) := by
  norm_num [sum_range_succ]
