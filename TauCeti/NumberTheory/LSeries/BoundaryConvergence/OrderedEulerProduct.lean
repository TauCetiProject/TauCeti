/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.PrimeCounting
import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.SumPrimePow

/-!
# Ordered Euler products from ordered prime-power sums

Let `c : ℕ → ℂ` satisfy `‖c p‖ ≤ 1` at every prime `p`, and let `a : ℕ → ℂ` be the coefficients
of the formal logarithm of the Euler product `∏ p, (1 - c p * p ^ (-s))⁻¹`: `a` vanishes off the
prime powers and `a (p ^ k) = c p ^ k / k` for `k ≥ 1`. For a Dirichlet character `χ` and
`c = χ`, these are the coefficients `χ n Λ n / log n`.

At `s = 1` neither the Dirichlet series `∑ a n / n` nor the Euler product need converge
absolutely, and only their ordered cutoffs make sense. This file compares the two cutoffs: the
difference between `∑ p ≤ N, log (1 - c p / p)⁻¹` and the partial sum `∑ n ≤ N, a n / n` tends to
zero. Hence if the ordered partial sums of `∑ a n / n` converge to `L`, then the ordered finite
products `∏ p ≤ N, (1 - c p / p)⁻¹` converge to `exp L`, and deleting the factors at a finite set
`S` of primes multiplies the limit by `∏ p ∈ S, (1 - c p / p)`.

The comparison is prime by prime. Regrouping by prime base,
`∑ n ≤ N, a n / n = ∑ p ≤ N, ∑ k ∈ [1, Nat.log p N], (c p / p) ^ k / k`, so the inner sum is a
partial sum of the Taylor series of `log (1 - c p / p)⁻¹`. Its truncation error is at most
`2 p ^ (-(Nat.log p N + 1))`, which is both less than `2 / N` and at most `2 / p ^ 2`; the sum
over `p ≤ N` of these errors tends to zero by dominated convergence. No unordered sum or product
at `s = 1` is asserted.

## Main results

* `TauCeti.LSeries.tendsto_sum_log_one_sub_inv_sub_sum_div`: the difference between the sum of
  local logarithms over `p ≤ N` and the partial sum `∑ n ∈ Icc 1 N, a n / n` tends to `0`;
  `TauCeti.LSeries.norm_sum_log_one_sub_inv_sub_sum_div_le` is the explicit bound
  `∑ p ≤ N, 2 / p ^ (Nat.log p N + 1)` on it.
* `TauCeti.LSeries.tendsto_prod_primesLE_inv_of_tendsto_sum`: if the partial sums converge to
  `L`, the finite Euler products converge to `exp L`.
* `TauCeti.LSeries.tendsto_prod_primesLE_filter_notMem_inv_of_tendsto_sum`: the same with the
  factors at a finite set of primes deleted.
* `TauCeti.LSeries.tendsto_prod_primesLE_filter_notMem_inv_iff`: independently of any partial
  sums, deleting the factors at a finite set `S` of primes transports convergence of the finite
  Euler products in both directions, multiplying the limit by `∏ p ∈ S, (1 - c p / p)`;
  `TauCeti.LSeries.tendsto_prod_primesLE_filter_notMem_inv_congr_iff` changes one finite set of
  deleted primes into another.
-/

public section

open Filter Finset Complex
open scoped Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ}

section FiniteDeletion

variable {S T : Finset ℕ}

/-- **Deleting finitely many Euler factors.** Let `S` be a finite set of primes with
`‖c p‖ ≤ 1` on `S`. The finite Euler products `∏ p ≤ N, (1 - c p / p)⁻¹` converge to `L` if and
only if the products over the primes `p ≤ N` outside `S` converge to
`L * ∏ p ∈ S, (1 - c p / p)`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_iff (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ 1) {L : ℂ} :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N with p ∉ S, (1 - c p / p)⁻¹) atTop
        (𝓝 (L * ∏ p ∈ S, (1 - c p / p))) ↔
      Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N, (1 - c p / p)⁻¹) atTop (𝓝 L) := by
  have hne : ∀ p ∈ S, 1 - c p / p ≠ 0 := fun p hp ↦
    one_sub_div_natCast_ne_zero (hS p hp).one_lt (hc p hp)
  rw [← Nat.tendsto_prod_primesLE_filter_notMem_iff hS fun p hp ↦ inv_ne_zero (hne p hp),
    prod_inv_distrib, mul_inv_cancel_right₀ (prod_ne_zero_iff.mpr hne)]

/-- **Changing the finite set of deleted Euler factors.** Let `S` and `T` be finite sets of primes
with `‖c p‖ ≤ 1` on both. The finite Euler products over the primes `p ≤ N` outside `S` converge
to `L * ∏ p ∈ S, (1 - c p / p)` if and only if those outside `T` converge to
`L * ∏ p ∈ T, (1 - c p / p)`: both say that the full products converge to `L`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_congr_iff (hS : ∀ p ∈ S, p.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hcS : ∀ p ∈ S, ‖c p‖ ≤ 1) (hcT : ∀ p ∈ T, ‖c p‖ ≤ 1) {L : ℂ} :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N with p ∉ S, (1 - c p / p)⁻¹) atTop
        (𝓝 (L * ∏ p ∈ S, (1 - c p / p))) ↔
      Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N with p ∉ T, (1 - c p / p)⁻¹) atTop
        (𝓝 (L * ∏ p ∈ T, (1 - c p / p))) := by
  rw [tendsto_prod_primesLE_filter_notMem_inv_iff hS hcS,
    tendsto_prod_primesLE_filter_notMem_inv_iff hT hcT]

end FiniteDeletion

section Comparison

variable (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) (ha : ∀ n, ¬IsPrimePow n → a n = 0)
  (ha_pow : ∀ p k : ℕ, p.Prime → k ≠ 0 → a (p ^ k) = c p ^ k / k)
include hc ha ha_pow

/-- The difference between the sum of the local logarithms `log (1 - c p / p)⁻¹` over the primes
`p ≤ N` and the partial sum `∑ n ∈ Icc 1 N, a n / n` of the coefficients of their Taylor
expansions is at most `∑ p ≤ N, 2 / p ^ (Nat.log p N + 1)`. -/
theorem norm_sum_log_one_sub_inv_sub_sum_div_le (N : ℕ) :
    ‖∑ p ∈ Nat.primesLE N, log (1 - c p / p)⁻¹ - ∑ n ∈ Icc 1 N, a n / n‖ ≤
      ∑ p ∈ Nat.primesLE N, 2 * ((p : ℝ) ^ (p.log N + 1))⁻¹ := by
  rw [Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log (f := fun n ↦ a n / n)
    (fun n hn ↦ by simp [ha n hn]) N, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun p hp ↦ ?_)
  have hpp := Nat.prime_of_mem_primesLE hp
  have key := norm_log_one_sub_div_inv_sub_sum_Icc_le hpp.two_le (hc p hpp) (p.log N)
  convert key using 4 with k hk
  rw [ha_pow p k hpp (by simp at hk; lia), div_pow]
  push_cast
  ring

/-- **The sum of local logarithms and the ordered partial sums agree in the limit.** Along the
ordered cutoffs `N → ∞`, the difference between `∑ p ≤ N, log (1 - c p / p)⁻¹` and
`∑ n ∈ Icc 1 N, a n / n` tends to `0`. -/
theorem tendsto_sum_log_one_sub_inv_sub_sum_div :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, log (1 - c p / p)⁻¹ - ∑ n ∈ Icc 1 N, a n / n)
      atTop (𝓝 0) := by
  refine squeeze_zero_norm (norm_sum_log_one_sub_inv_sub_sum_div_le hc ha ha_pow) ?_
  simpa [← mul_sum] using Nat.tendsto_sum_primesLE_inv_pow_log_succ.const_mul 2

/-- **Ordered Euler products from ordered partial sums.** If the ordered partial sums
`∑ n ∈ Icc 1 N, a n / n` converge to `L`, then the finite Euler products
`∏ p ≤ N, (1 - c p / p)⁻¹` converge to `exp L`; in particular, their limit is nonzero. -/
theorem tendsto_prod_primesLE_inv_of_tendsto_sum {L : ℂ}
    (hL : Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N, (1 - c p / p)⁻¹) atTop (𝓝 (exp L)) := by
  have hlog : Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, log (1 - c p / p)⁻¹) atTop (𝓝 L) := by
    simpa using (tendsto_sum_log_one_sub_inv_sub_sum_div hc ha ha_pow).add hL
  refine ((continuous_exp.tendsto L).comp hlog).congr fun N ↦ ?_
  rw [Function.comp_apply, exp_sum]
  refine prod_congr rfl fun p hp ↦ exp_log (inv_ne_zero ?_)
  have hpp := Nat.prime_of_mem_primesLE hp
  exact one_sub_div_natCast_ne_zero hpp.one_lt (hc p hpp)

/-- **Deleting finitely many Euler factors.** If the ordered partial sums
`∑ n ∈ Icc 1 N, a n / n` converge to `L` and `S` is a finite set of primes, then the finite Euler
products over the primes `p ≤ N` outside `S` converge to `exp L * ∏ p ∈ S, (1 - c p / p)`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_of_tendsto_sum {L : ℂ}
    (hL : Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n) atTop (𝓝 L)) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N with p ∉ S, (1 - c p / p)⁻¹) atTop
      (𝓝 (exp L * ∏ p ∈ S, (1 - c p / p))) :=
  (tendsto_prod_primesLE_filter_notMem_inv_iff hS fun p hp ↦ hc p (hS p hp)).mpr
    (tendsto_prod_primesLE_inv_of_tendsto_sum hc ha ha_pow hL)

end Comparison

end TauCeti.LSeries
