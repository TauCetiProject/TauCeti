/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Series
public import TauCeti.Topology.Algebra.InfiniteSum.IntegralCoefficients
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Evaluating divisor-sum series

The integral divisor-sum series converges at a parameter of norm less than one in a complete
seminormed ring, since its coefficients grow polynomially. Its value is the sum of its evaluated
coefficients; in a non-archimedean ring its norm is at most that of the parameter. In any
seminormed ring with `‖1‖ = 1`, regrouping the series by divisors as the Lambert series
`∑ d ^ k qᵈ / (1 - qᵈ)` bounds its norm by `(∑ n ^ k ‖q‖ ^ n) / (1 - ‖q‖)`, a bound that is
sharp to first order in `‖q‖` and so suited to explicit numerical estimates of Eisenstein series.
When the target is normed and commutative, `evalIntSeries_divisorSumSeries`
identifies evaluation of the formal series `divisorSumSeries k` under `evalIntSeries` with its
analytic value `divisorSumAt k q`.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [SeminormedRing K]

/-- The divisor-sum series `s_k(q) = ∑ σ_k(n) q^n` converges for `‖q‖ < 1`: its coefficients are at
most `n ^ (k + 1)`. -/
theorem summable_divisorSumSeries [CompleteSpace K] (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (((σ k n : ℕ) : ℤ) : K) * q ^ n) := by
  refine .of_norm_bounded ((summable_pow_mul_geometric_of_norm_lt_one (k + 1)
    (by rwa [Real.norm_of_nonneg (norm_nonneg q)])).mul_left ‖(1 : K)‖) fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  calc ‖(((σ k n : ℕ) : ℤ) : K) * q ^ n‖ ≤ (σ k n : ℝ) * ‖(1 : K)‖ * ‖q‖ ^ n := by
        rw [Int.cast_natCast]
        exact (norm_mul_le _ _).trans (mul_le_mul (Nat.norm_cast_le _) (norm_pow_le' q hn)
          (norm_nonneg _) (by positivity))
    _ ≤ ‖(1 : K)‖ * ((n : ℝ) ^ (k + 1) * ‖q‖ ^ n) := by
        rw [mul_comm (σ k n : ℝ), mul_assoc]
        gcongr
        exact_mod_cast sigma_le_pow_succ k n

/-- Evaluation of the integral divisor-sum series in a seminormed ring. In a complete ring it
converges for `‖q‖ < 1` (`summable_divisorSumSeries`). -/
noncomputable def divisorSumAt (k : ℕ) (q : K) : K :=
  ∑' n : ℕ, (((σ k n : ℕ) : ℤ) : K) * q ^ n

/-- The value of a divisor-sum series is its defining sum. -/
theorem divisorSumAt_def (k : ℕ) (q : K) :
    divisorSumAt k q = ∑' n : ℕ, (((σ k n : ℕ) : ℤ) : K) * q ^ n := by
  simp only [divisorSumAt]

/-- The divisor-sum series as a sum over positive integers, `s_k(q) = ∑_{n ≥ 1} σ_k(n) qⁿ`, the
form in which Mathlib states the `q`-expansions of Eisenstein series. -/
theorem divisorSumAt_eq_tsum_pnat (k : ℕ) (q : K) :
    divisorSumAt k q = ∑' n : ℕ+, (σ k n : K) * q ^ (n : ℕ) := by
  rw [divisorSumAt_def, tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ ↦ (σ k n : K) * q ^ n)
    (by simp)]
  simp

/-- Continuous ring homomorphisms commute with convergent divisor-sum series. -/
theorem map_divisorSumAt [CompleteSpace K] {L : Type*} [NormedRing L] (f : K →+* L)
    (hf : Continuous f)
    (k : ℕ) (q : K) (hq : ‖q‖ < 1) : f (divisorSumAt k q) = divisorSumAt k (f q) := by
  rw [divisorSumAt_def, divisorSumAt_def,
    Summable.map_tsum (summable_divisorSumSeries k hq) f hf]
  apply tsum_congr
  intro n
  simp

/-- Evaluating the integral divisor-sum series gives its convergent analytic value. -/
@[simp] theorem evalIntSeries_divisorSumSeries {K : Type*} [NormedCommRing K]
    [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) (q : K) (hq : ‖q‖ < 1) :
    evalIntSeries q hq (divisorSumSeries k) = divisorSumAt k q := by
  simp only [evalIntSeries_apply, coeff_divisorSumSeries, divisorSumAt_def]

/-- In a non-archimedean ring the divisor-sum series has no constant term, so `‖s_k(q)‖ ≤ ‖q‖` for
`‖q‖ < 1`. -/
theorem norm_divisorSumAt_le [IsUltrametricDist K] (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    ‖divisorSumAt k q‖ ≤ ‖q‖ := by
  rw [divisorSumAt_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  calc ‖(((σ k n : ℕ) : ℤ) : K) * q ^ n‖ = ‖((σ k n : ℕ) : ℤ) • q ^ n‖ := by rw [zsmul_eq_mul]
    _ ≤ ‖q ^ n‖ := IsUltrametricDist.norm_zsmul_le _ _
    _ ≤ ‖q‖ ^ n := norm_pow_le' q hn
    _ ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg _) hq.le hn.ne'

/-- **The Lambert bound for the divisor-sum series.** In a seminormed ring with `‖1‖ = 1`,
`‖s_k(q)‖ ≤ (∑ n ^ k ‖q‖ ^ n) / (1 - ‖q‖)` for `‖q‖ < 1`. -/
theorem norm_divisorSumAt_le_tsum_div_one_sub [NormOneClass K] (k : ℕ) {q : K} (hq : ‖q‖ < 1) :
    ‖divisorSumAt k q‖ ≤ (∑' n : ℕ, (n : ℝ) ^ k * ‖q‖ ^ n) / (1 - ‖q‖) := by
  set r := ‖q‖
  have hr0 : 0 ≤ r := norm_nonneg q
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  have hsum : Summable fun n : ℕ ↦ (σ k n : ℝ) * r ^ n := by
    simpa using summable_divisorSumSeries (K := ℝ) k hr
  have hpow : Summable fun n : ℕ ↦ (n : ℝ) ^ k * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  rw [divisorSumAt_def]
  refine (tsum_of_norm_bounded hsum.hasSum fun n ↦ ?_).trans ?_
  · refine (norm_mul_le _ _).trans (mul_le_mul ?_ (norm_pow_le q n) (norm_nonneg _)
      (Nat.cast_nonneg _))
    simpa using Nat.norm_cast_le (α := K) (σ k n)
  rw [← tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ ↦ (σ k n : ℝ) * r ^ n) (by simp),
    ← tsum_pow_div_one_sub_eq_tsum_sigma hr k,
    hpow.tsum_eq_zero_add, ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ (n : ℝ) ^ k * r ^ n)]
  have hpnat := hpow.comp_injective PNat.coe_injective
  calc ∑' n : ℕ+, (n : ℝ) ^ k * r ^ (n : ℕ) / (1 - r ^ (n : ℕ))
      ≤ ∑' n : ℕ+, (n : ℝ) ^ k * r ^ (n : ℕ) / (1 - r) := by
        refine ((summable_norm_pow_mul_geometric_div_one_sub k hr).comp_injective
          PNat.coe_injective).tsum_le_tsum (fun n ↦ ?_) (hpnat.div_const _)
        have : r ^ (n : ℕ) ≤ r := pow_le_of_le_one hr0 hq.le n.ne_zero
        gcongr
    _ = (∑' n : ℕ+, (n : ℝ) ^ k * r ^ (n : ℕ)) / (1 - r) := tsum_div_const
    _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

end TauCeti

end
