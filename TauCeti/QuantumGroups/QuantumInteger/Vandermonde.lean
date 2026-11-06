/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Binomial
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Vandermonde convolution for symmetric quantum binomials

The symmetric normalization gives the convolution
`[m+n choose r]_q = ∑_{a+b=r} q^(n*a-m*b) [m choose a]_q [n choose b]_q`.
We prove it for every nonzero parameter in a semifield, including roots of unity and
`q = 1`. In particular no quantum factorial is cancelled. This is the nonnegative-upper-index
identity underlying convolution of integral Gaussian coefficients and toral weight formulas.

## References

* G. Lusztig, *Introduction to Quantum Groups*, §1.3, for symmetric Gaussian coefficients.
* V. Kac and P. Cheung, *Quantum Calculus*, Chapter 5, for quantum binomial identities.
-/

public section

namespace TauCeti

open Finset

variable {K : Type*} [Semifield K] {q : K}

private lemma vandermonde_step (hq : q ≠ 0) (m n a b : ℕ) {r : ℕ}
    (hab : a + b = r) :
    q ^ ((n : ℤ) * (a + 1) - (m + 1) * b) *
        quantumBinomial q (m + 1) (a + 1) * quantumBinomial q n b =
      q ^ ((m : ℤ) + n - r) *
          (q ^ ((n : ℤ) * a - m * b) *
            quantumBinomial q m a * quantumBinomial q n b) +
        q ^ (-((r : ℤ) + 1)) *
          (q ^ ((n : ℤ) * (a + 1) - m * b) *
            quantumBinomial q m (a + 1) * quantumBinomial q n b) := by
  subst r
  push_cast
  by_cases ha : a ≤ m
  · rw [quantumBinomial_succ_succ]
    have hp : q ^ (m - a) = q ^ ((m : ℤ) - a) := by
      rw [← Nat.cast_sub ha, zpow_natCast]
    have hi : q⁻¹ ^ (a + 1) = q ^ (-((a : ℤ) + 1)) := by
      rw [zpow_neg, ← Nat.cast_add_one, zpow_natCast, inv_pow]
    rw [hp, hi]
    simp only [mul_add, add_mul, ← mul_assoc, ← zpow_add₀ hq]
    congr 4 <;> ring
  · have hm : m < a := by omega
    simp [quantumBinomial_eq_zero_of_lt q hm,
      quantumBinomial_eq_zero_of_lt q (by omega : m < a + 1),
      quantumBinomial_eq_zero_of_lt q (by omega : m + 1 < a + 1)]

/-- **Quantum Vandermonde convolution**, in the symmetric normalization. The exponent is
`n*a-m*b`, and the formula remains valid at roots of unity because it involves no division
by quantum integers. -/
theorem quantumBinomial_add (hq : q ≠ 0) (m n r : ℕ) :
    quantumBinomial q (m + n) r =
      ∑ p ∈ antidiagonal r, q ^ ((n : ℤ) * p.1 - (m : ℤ) * p.2) *
        quantumBinomial q m p.1 * quantumBinomial q n p.2 := by
  induction m generalizing r with
  | zero =>
    rw [zero_add, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [sum_eq_single 0]
    · simp
    · intro a ha hne
      simp [quantumBinomial_eq_zero_of_lt q (Nat.pos_of_ne_zero hne)]
    · simp
  | succ m ih =>
    cases r with
    | zero => simp
    | succ r =>
      have hpascal : quantumBinomial q (m + 1 + n) (r + 1) =
          q ^ ((m : ℤ) + n - r) * quantumBinomial q (m + n) r +
            q ^ (-((r : ℤ) + 1)) * quantumBinomial q (m + n) (r + 1) := by
        rw [Nat.succ_add, quantumBinomial_succ_succ]
        congr 1
        · by_cases hr : r ≤ m + n
          · rw [← zpow_natCast q (m + n - r), Nat.cast_sub hr, Nat.cast_add]
          · simp [quantumBinomial_eq_zero_of_lt q (by omega : m + n < r)]
        · rw [zpow_neg, ← Nat.cast_add_one, zpow_natCast, inv_pow]
      rw [hpascal, ih, ih, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [sum_congr rfl (fun p hp => vandermonde_step hq m n p.1 p.2
        (mem_antidiagonal.mp hp)), sum_add_distrib, ← mul_sum, ← mul_sum]
      simp only [Nat.cast_zero, mul_zero, zero_sub, quantumBinomial_zero_right, mul_one]
      rw [mul_add]
      have hb : q ^ (-((r : ℤ) + 1)) *
          (q ^ (-((m : ℤ) * (r + 1))) * quantumBinomial q n (r + 1)) =
            q ^ (-(((m : ℤ) + 1) * (r + 1))) * quantumBinomial q n (r + 1) := by
        rw [← mul_assoc, ← zpow_add₀ hq]
        congr 2
        ring
      rw [hb]
      ac_rfl

end TauCeti
