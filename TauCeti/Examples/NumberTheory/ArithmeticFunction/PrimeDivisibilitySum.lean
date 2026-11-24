/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.PrimeDivisibilitySum
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Simproc.Factors

/-!
# Examples of weighted prime divisibility sums

Take `P = {2, 3}` with weights `a p = p`.
* The value at `12` is `2 + 3 = 5`, not `2 * 2 + 3 = 7`: prime powers are counted once.
* The value at `0` is `0`, although every member of `P` divides `0`.
* At the prime powers `2 ^ 3` and `5 ^ 1` the values are `2` and `0`.

With unit weights over the prime factors of `12` the value at `12` is `ω 12 = 2`, while
`Ω 12 = 3`. For `P = {2}` and weight `2`, the values at `4` and `2` are both `2`, so the coprime
law fails for the non-coprime pair `2, 2`. Weights cancel pointwise, and weights outside `P` are
never seen.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

-- Prime powers are counted once: the value at `12 = 2 ^ 2 * 3` is `2 + 3`.
example : primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) 12 = 5 := by
  rw [primeDivisibilitySum_apply _ _ (by norm_num)]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Nat.dvd_iff_mod_eq_zero]

-- The value at zero is zero, although the unguarded sum would be `2 + 3`.
example : primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) 0 = 0 := by
  simp

-- The value at one vanishes for every set of primes and every weight.
example (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℝ) : primeDivisibilitySum P a 1 = 0 :=
  (isStronglyAdditive_primeDivisibilitySum hP a).map_one

-- Prime-power evaluation at `2 ^ 3` and `5 ^ 1`.
example : primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) (2 ^ 3) = 2 ∧
    primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) (5 ^ 1) = 0 := by
  have hP : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by decide
  rw [primeDivisibilitySum_apply_prime_pow hP _ Nat.prime_two three_ne_zero,
    primeDivisibilitySum_apply_prime_pow hP _ Nat.prime_five one_ne_zero]
  norm_num

-- Unit weights over the prime factors of `12` count distinct prime factors, `ω 12 = 2`, and not
-- prime factors with multiplicity, `Ω 12 = 3`.
example : primeDivisibilitySum (Nat.primeFactors 12) (1 : ℕ → ℝ) 12 = 2 ∧
    (Ω 12 : ℝ) = 3 := by
  rw [primeDivisibilitySum_primeFactors_one]
  norm_num [cardDistinctFactors_eq_length_dedup_primeFactorsList,
    cardFactors_apply, Nat.primeFactorsList_ofNat]

-- The coprime law fails without coprimality: for `P = {2}` and weight `2`, the value at `4` is `2`
-- while the values at `2` and `2` add to `4`.
example : primeDivisibilitySum {2} (fun _ => (2 : ℝ)) (2 * 2) ≠
    primeDivisibilitySum {2} (fun _ => (2 : ℝ)) 2 +
      primeDivisibilitySum {2} (fun _ => (2 : ℝ)) 2 := by
  rw [primeDivisibilitySum_apply _ _ (by norm_num), primeDivisibilitySum_apply _ _ (by norm_num)]
  norm_num [Finset.filter_singleton, Nat.dvd_iff_mod_eq_zero]

-- Opposite weights cancel: the weighted divisibility sum is not a convolution formula.
example (P : Finset ℕ) (a : ℕ → ℝ) :
    primeDivisibilitySum P a + primeDivisibilitySum P (-a) = 0 := by
  rw [← primeDivisibilitySum_add, add_neg_cancel, primeDivisibilitySum_zero]

-- Changing the weights outside `P` has no effect.
example : primeDivisibilitySum {2, 3} (fun p => (p : ℝ)) =
    primeDivisibilitySum {2, 3} (fun p => if p = 5 then 0 else (p : ℝ)) :=
  primeDivisibilitySum_congr (by simp)
