/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds
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
-/

public section

open Filter Finset Complex
open scoped Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ}

/-- For `2 ≤ p` and `‖w‖ ≤ 1`, the partial sum of the Taylor series of `log (1 - w / p)⁻¹` up to
degree `K` is within `2 / p ^ (K + 1)` of it. This is the local comparison at a single prime. -/
private theorem norm_log_one_sub_div_inv_sub_sum_Icc_le {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hw : ‖w‖ ≤ 1) (K : ℕ) :
    ‖log (1 - w / p)⁻¹ - ∑ k ∈ Icc 1 K, (w / p) ^ k / k‖ ≤ 2 * ((p : ℝ) ^ (K + 1))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp
  have hz : ‖w / p‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_div, norm_natCast, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) hw
  have hz1 : ‖w / p‖ ≤ 1 / 2 := hz.trans (by rw [one_div]; gcongr)
  have hpos : 0 < 1 - ‖w / p‖ := by linarith
  refine (norm_log_one_sub_inv_sub_sum_Icc_le K (by linarith)).trans ?_
  have h2 : (1 - ‖w / p‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos two_pos]
    linarith
  calc ‖w / p‖ ^ (K + 1) * (1 - ‖w / p‖)⁻¹ / (K + 1)
      ≤ ‖w / p‖ ^ (K + 1) * (1 - ‖w / p‖)⁻¹ :=
        div_le_self (by have := inv_pos.mpr hpos; positivity) (by simp)
    _ ≤ ((p : ℝ)⁻¹) ^ (K + 1) * 2 := by gcongr
    _ = 2 * ((p : ℝ) ^ (K + 1))⁻¹ := by rw [inv_pow, mul_comm]

/-- For `1 < p` and `‖w‖ ≤ 1`, the Euler factor `1 - w / p` is nonzero. -/
private theorem one_sub_div_ne_zero {p : ℕ} (hp : 1 < p) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    1 - w / p ≠ 0 := by
  refine sub_ne_zero.mpr fun h ↦ ?_
  have h1 : ‖w / p‖ = 1 := by rw [← h, norm_one]
  have h2 : (1 : ℝ) < p := mod_cast hp
  rw [norm_div, norm_natCast, div_eq_one_iff_eq (by positivity)] at h1
  linarith

/-- The error bounds `p ^ (-(Nat.log p N + 1))`, summed over the primes `p ≤ N`, tend to `0`:
each is less than `1 / N`, and they are dominated by the summable `1 / p ^ 2`. -/
private theorem tendsto_sum_primesLE_inv_pow_log_succ :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Nat.primesLE N, ((p : ℝ) ^ (p.log N + 1))⁻¹) atTop (𝓝 0) := by
  set e : ℕ → ℕ → ℝ := fun N p ↦ if p ∈ Nat.primesLE N then ((p : ℝ) ^ (p.log N + 1))⁻¹ else 0
  have hsum (N : ℕ) : ∑ p ∈ Nat.primesLE N, ((p : ℝ) ^ (p.log N + 1))⁻¹ = ∑' p, e N p := by
    rw [tsum_eq_sum (s := Nat.primesLE N) fun p hp ↦ by simp [e, hp]]
    exact sum_congr rfl fun p hp ↦ by simp [e, hp]
  simp_rw [hsum]
  have hzero : (0 : ℝ) = ∑' _ : ℕ, (0 : ℝ) := tsum_zero.symm
  rw [hzero]
  refine tendsto_tsum_of_dominated_convergence (bound := fun p : ℕ ↦ ((p : ℝ) ^ 2)⁻¹)
    (Real.summable_nat_pow_inv.mpr one_lt_two) (fun p ↦ ?_) (Eventually.of_forall fun N p ↦ ?_)
  · -- For fixed `p`, the term is eventually at most `1 / N`, since `N < p ^ (Nat.log p N + 1)`.
    refine squeeze_zero' (Eventually.of_forall fun N ↦ ?_) ?_
      tendsto_inv_atTop_nhds_zero_nat
    · simp only [e]
      split_ifs <;> positivity
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simp only [e]
      split_ifs with hp
      · have h := Nat.lt_pow_succ_log_self (Nat.one_lt_of_mem_primesLE hp) N
        exact inv_anti₀ (mod_cast hN) (mod_cast h.le)
      · positivity
  · -- For `p ≤ N`, the exponent `Nat.log p N + 1` is at least `2`.
    simp only [e]
    split_ifs with hp
    · have hp1 := Nat.one_lt_of_mem_primesLE hp
      have hlog : 1 ≤ p.log N := Nat.log_pos hp1 (Nat.le_of_mem_primesLE hp)
      rw [norm_inv, norm_pow, Real.norm_natCast]
      exact inv_anti₀ (by positivity)
        (pow_le_pow_right₀ (mod_cast hp1.le) (by lia))
    · simp only [norm_zero]
      positivity

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
  simpa [← mul_sum] using tendsto_sum_primesLE_inv_pow_log_succ.const_mul 2

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
  exact one_sub_div_ne_zero hpp.one_lt (hc p hpp)

/-- **Deleting finitely many Euler factors.** If the ordered partial sums
`∑ n ∈ Icc 1 N, a n / n` converge to `L` and `S` is a finite set of primes, then the finite Euler
products over the primes `p ≤ N` outside `S` converge to `exp L * ∏ p ∈ S, (1 - c p / p)`. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_of_tendsto_sum {L : ℂ}
    (hL : Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, a n / n) atTop (𝓝 L)) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ Nat.primesLE N with p ∉ S, (1 - c p / p)⁻¹) atTop
      (𝓝 (exp L * ∏ p ∈ S, (1 - c p / p))) := by
  refine ((tendsto_prod_primesLE_inv_of_tendsto_sum hc ha ha_pow hL).mul_const _).congr' ?_
  filter_upwards [eventually_ge_atTop (S.sup id)] with N hN
  have hSN : S ⊆ Nat.primesLE N := fun p hp ↦
    Nat.mem_primesLE.mpr ⟨(le_sup (f := id) hp).trans hN, hS p hp⟩
  rw [← prod_filter_mul_prod_filter_not (Nat.primesLE N) (· ∈ S), filter_mem_eq_inter,
    inter_eq_right.mpr hSN, mul_right_comm, ← prod_mul_distrib,
    prod_eq_one fun p hp ↦
      inv_mul_cancel₀ (one_sub_div_ne_zero (hS p hp).one_lt (hc p (hS p hp))), one_mul]

end Comparison

end TauCeti.LSeries
