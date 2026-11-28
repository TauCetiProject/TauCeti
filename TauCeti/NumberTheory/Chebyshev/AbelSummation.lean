/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import TauCeti.NumberTheory.AbelSummation

/-!
# Abel summation against the Chebyshev function

A weighted logarithmic prime sum on `(a, b]` equals a difference of boundary terms
minus the integral of the weight's derivative against `θ`. The derivative may be singular
at either endpoint if the weight is continuous on `[a, b]` and its interior derivative is
interval integrable.
-/

public section

namespace TauCeti

open Finset MeasureTheory Set

/-- A prime-supported sum over `(⌊a⌋₊, ⌊b⌋₊]` is a sum over the primes in `(a, b]`. -/
theorem sum_Ioc_mul_ite_prime_eq_sum_filter_primesLE {a b : ℝ} (f g : ℕ → ℝ) :
    ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * (if n.Prime then g n else 0) =
      ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), f p * g p := by
  rw [Nat.primesLE_eq_filter_Icc_zero]
  simp only [mul_ite, mul_zero, ← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, Finset.mem_Icc, Finset.mem_Ioc, zero_le, true_and]
  by_cases hp : n.Prime
  · simp [hp, Nat.floor_lt' hp.ne_zero, and_comm]
  · simp [hp]

/-- Abel summation against `θ` on `(a, b]` for a continuous weight with an integrable
interior derivative. -/
theorem sum_filter_primesLE_mul_log_eq_sub_sub_integral {g g' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) (hg' : IntervalIntegrable g' volume a b) :
    ∑ p ∈ (Nat.primesLE ⌊b⌋₊).filter (fun p : ℕ ↦ a < (p : ℝ)), g p * Real.log p =
      g b * Chebyshev.theta b - g a * Chebyshev.theta a -
        ∫ t in a..b, g' t * Chebyshev.theta t := by
  have h := sum_mul_eq_sub_sub_integral_mul_of_hasDerivAt
    (fun p : ℕ ↦ if p.Prime then Real.log p else 0) hab hc hg hg'
  rw [sum_Ioc_mul_ite_prime_eq_sum_filter_primesLE] at h
  simpa only [← sum_filter, ← Chebyshev.theta_eq_sum_Icc] using h

end TauCeti
