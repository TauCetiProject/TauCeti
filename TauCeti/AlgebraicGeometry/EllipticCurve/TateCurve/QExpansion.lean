/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Tactic.LinearCombination

/-!
# Tate coordinates on the unit circle

For a multiplicative parameter `u` of norm one, the Tate coordinates have convergent expansions
in `q`, with Laurent-polynomial coefficients in `u`. Their constant terms are the rational
parametrization `u / (1 - u)²`, `u² / (1 - u)³` of the nodal cubic. All remaining coefficients
are finite divisor sums.

These expansions cover the boundary of the fundamental annulus, which is not covered by
geometric expansion in `u` and `q / u`: when `‖u‖ = 1`, the term at index zero must instead be
kept as a rational function. They supply the analytic comparison needed to specialize formal
identities in `q` at such parameters. No curve equation or uniformisation homomorphism is
asserted here. At `u = 1` the rational terms retain the totalized field values.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- On the unit circle, the first Tate coordinate is a convergent `q`-expansion with finite
Laurent-polynomial coefficients. Its constant term is `u / (1 - u)²`. -/
theorem tateUniformizationX_eq_qExpansion (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) :
    tateUniformizationX q u = (u : K) / (1 - (u : K)) ^ 2 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n := by
  have hui : ‖(u : K)⁻¹‖ = 1 := by simp [hu]
  have hp := (hasSum_bounded_sum_divisors_mul_pow
    (fun d ↦ (d : K) * (u : K) ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using IsUltrametricDist.norm_natCast_le_one K d) hq).summable
  have hm := (hasSum_bounded_sum_divisors_mul_pow
    (fun d ↦ (d : K) * (u : K)⁻¹ ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using IsUltrametricDist.norm_natCast_le_one K d) hq).summable
  have hsmall (v : K) (hv : ‖v‖ = 1) (n : ℕ+) : ‖(q : K) ^ (n : ℕ) * v‖ < 1 := by
    rw [norm_mul, norm_pow, hv, mul_one]
    exact pow_lt_one₀ (norm_nonneg _) hq n.ne_zero
  have hs := summable_divisorSumSeries (K := K) 1 hq
  -- Isolate the rational term at index zero and expand the two strictly convergent tails.
  have hsplit := tsum_int_eq_zero_add_tsum_pnat (summable_tateUniformizationX q hq u)
  simp only [zpow_natCast, zpow_neg] at hsplit
  have hneg (n : ℕ+) :
      ((q : K) ^ (n : ℕ))⁻¹ * (u : K) /
          (1 - ((q : K) ^ (n : ℕ))⁻¹ * (u : K)) ^ 2 =
        ((q : K) ^ (n : ℕ) * (u : K)⁻¹) /
          (1 - (q : K) ^ (n : ℕ) * (u : K)⁻¹) ^ 2 := by
    simpa only [mul_inv, inv_inv] using
      inv_div_one_sub_inv_sq ((q : K) ^ (n : ℕ) * (u : K)⁻¹)
  rw [tateUniformizationX_def, hsplit]
  simp_rw [hneg, ← tsum_natCast_succ_mul_pow_succ _ (hsmall _ hu _),
    ← tsum_natCast_succ_mul_pow_succ _ (hsmall _ hui _)]
  have he := tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors (fun d ↦ (d : K))
    (IsUltrametricDist.norm_natCast_le_one K) hq hu.le
  have hei := tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors (fun d ↦ (d : K))
    (IsUltrametricDist.norm_natCast_le_one K) hq hui.le
  rw [he, hei]
  -- Regroup both tails and the divisor-sum correction coefficient by coefficient.
  suffices h :
      (∑' n : ℕ, (∑ d ∈ n.divisors, (d : K) * (u : K) ^ d) * (q : K) ^ n) +
      (∑' n : ℕ, (∑ d ∈ n.divisors, (d : K) * (u : K)⁻¹ ^ d) * (q : K) ^ n) -
      2 * divisorSumAt 1 (q : K) =
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n by
    simp only [zpow_zero, one_mul]
    linear_combination h
  rw [divisorSumAt_def, ← tsum_mul_left, ← hp.tsum_add hm, ← (hp.add hm).tsum_sub (hs.mul_left 2)]
  apply tsum_congr
  intro n
  simp only [sigma_one_apply]
  push_cast
  rw [← add_mul, ← mul_assoc, ← sub_mul, ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- On the unit circle, the second Tate coordinate is a convergent `q`-expansion with finite
Laurent-polynomial coefficients. Its constant term is `u² / (1 - u)³`; the binomial coefficients
are integers before specialization, so the formula also applies in characteristics two and three. -/
theorem tateUniformizationY_eq_qExpansion (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) :
    tateUniformizationY q u = (u : K) ^ 2 / (1 - (u : K)) ^ 3 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n := by
  have hui : ‖(u : K)⁻¹‖ = 1 := by simp [hu]
  have hp := (hasSum_bounded_sum_divisors_mul_pow
    (fun d ↦ (d.choose 2 : K) * (u : K) ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using
        IsUltrametricDist.norm_natCast_le_one K (d.choose 2)) hq).summable
  have hm := (hasSum_bounded_sum_divisors_mul_pow
    (fun d ↦ -((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using
        IsUltrametricDist.norm_natCast_le_one K ((d + 1).choose 2)) hq).summable
  have hsmall (v : K) (hv : ‖v‖ = 1) (n : ℕ+) : ‖(q : K) ^ (n : ℕ) * v‖ < 1 := by
    rw [norm_mul, norm_pow, hv, mul_one]
    exact pow_lt_one₀ (norm_nonneg _) hq n.ne_zero
  have hs := summable_divisorSumSeries (K := K) 1 hq
  -- The negative-index tail has coefficients minus choose (d + 1) 2, rather than choose d 2.
  have hsplit := tsum_int_eq_zero_add_tsum_pnat (summable_tateUniformizationY q hq u)
  simp only [zpow_natCast, zpow_neg] at hsplit
  have hneg (n : ℕ+) :
      (((q : K) ^ (n : ℕ))⁻¹ * (u : K)) ^ 2 /
          (1 - ((q : K) ^ (n : ℕ))⁻¹ * (u : K)) ^ 3 =
        -((q : K) ^ (n : ℕ) * (u : K)⁻¹) /
          (1 - (q : K) ^ (n : ℕ) * (u : K)⁻¹) ^ 3 := by
    simpa only [mul_inv, inv_inv] using
      inv_sq_div_one_sub_inv_cube ((q : K) ^ (n : ℕ) * (u : K)⁻¹)
  rw [tateUniformizationY_def, hsplit]
  simp_rw [hneg, ← tsum_choose_two_mul_pow_succ _ (hsmall _ hu _),
    ← tsum_neg_choose_two_mul_pow_succ _ (hsmall _ hui _)]
  have he := tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors (fun d ↦ (d.choose 2 : K))
    (fun d ↦ IsUltrametricDist.norm_natCast_le_one K (d.choose 2)) hq hu.le
  have hei := tsum_bounded_mul_pow_mul_eq_tsum_sum_divisors (fun d ↦ -((d + 1).choose 2 : K))
    (fun d ↦ by simpa using IsUltrametricDist.norm_natCast_le_one K ((d + 1).choose 2)) hq hui.le
  rw [he, hei]
  -- Absolute convergence permits combining the two tails with the divisor-sum correction.
  suffices h :
      (∑' n : ℕ, (∑ d ∈ n.divisors, (d.choose 2 : K) * (u : K) ^ d) * (q : K) ^ n) +
      (∑' n : ℕ, (∑ d ∈ n.divisors, -((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d) *
        (q : K) ^ n) + divisorSumAt 1 (q : K) =
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n by
    simp only [zpow_zero, one_mul]
    linear_combination h
  rw [divisorSumAt_def, ← hp.tsum_add hm, ← (hp.add hm).tsum_add hs]
  apply tsum_congr
  intro n
  simp only [sigma_one_apply]
  push_cast
  rw [← add_mul, ← add_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  ring

end TauCeti

end
