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

## Main results

* `hasSum_tateUniformizationX_sub_of_norm_eq_one` and
  `hasSum_tateUniformizationY_sub_of_norm_eq_one` give convergence and values of the
  divisor-sum series after removing the rational constant terms.
* `tateUniformizationX_eq_add_tsum_sum_divisors_of_norm_eq_one` and
  `tateUniformizationY_eq_add_tsum_sum_divisors_of_norm_eq_one` give the corresponding
  coordinate identities.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_pow_pnat_mul_lt_one {q v : K} (hq : ‖q‖ < 1) (hv : ‖v‖ = 1)
    (n : ℕ+) : ‖q ^ (n : ℕ) * v‖ < 1 := by
  rw [norm_mul, norm_pow, hv, mul_one]
  exact pow_lt_one₀ (norm_nonneg _) hq n.ne_zero

/-- On the unit circle, the first Tate coordinate is a convergent `q`-expansion with finite
Laurent-polynomial coefficients. Its constant term is `u / (1 - u)²`. -/
theorem hasSum_tateUniformizationX_sub_of_norm_eq_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n)
      (tateUniformizationX q u - (u : K) / (1 - (u : K)) ^ 2) := by
  have hui : ‖(u : K)⁻¹‖ = 1 := by simp [hu]
  have hp := (hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (C := 1) (k := 0)
    (fun d ↦ (d : K) * (u : K) ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using IsUltrametricDist.norm_natCast_le_one K d) hq).summable
  have hm := (hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (C := 1) (k := 0)
    (fun d ↦ (d : K) * (u : K)⁻¹ ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using IsUltrametricDist.norm_natCast_le_one K d) hq).summable
  have hs := summable_divisorSumSeries (K := K) 1 hq
  suffices h : HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n)
      ((∑' n : ℕ, (∑ d ∈ n.divisors, (d : K) * (u : K) ^ d) * (q : K) ^ n) +
      (∑' n : ℕ, (∑ d ∈ n.divisors, (d : K) * (u : K)⁻¹ ^ d) * (q : K) ^ n) -
      2 * divisorSumAt 1 (q : K)) by
    convert h using 1
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
    simp_rw [hneg, ← tsum_natCast_succ_mul_pow_succ _ (norm_pow_pnat_mul_lt_one hq hu _),
      ← tsum_natCast_succ_mul_pow_succ _ (norm_pow_pnat_mul_lt_one hq hui _)]
    have he := tsum_tsum_mul_pow_eq_tsum_sum_divisors_of_norm_le_mul_pow (C := 1) (k := 0)
      (fun d ↦ (d : K))
      (fun d ↦ by simpa using IsUltrametricDist.norm_natCast_le_one K d) hq hu.le
    have hei := tsum_tsum_mul_pow_eq_tsum_sum_divisors_of_norm_le_mul_pow (C := 1) (k := 0)
      (fun d ↦ (d : K))
      (fun d ↦ by simpa using IsUltrametricDist.norm_natCast_le_one K d) hq hui.le
    rw [he, hei]
    simp only [zpow_zero, one_mul]
    ring
  convert (hp.hasSum.add hm.hasSum).sub (hs.hasSum.mul_left 2) using 1
  · funext n
    simp only [sigma_one_apply]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · simp only [divisorSumAt_def]

/-- The first Tate coordinate equals its unit-circle divisor-sum expansion.
Convergence is given by `hasSum_tateUniformizationX_sub_of_norm_eq_one`. -/
theorem tateUniformizationX_eq_add_tsum_sum_divisors_of_norm_eq_one
    (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu : ‖(u : K)‖ = 1) :
    tateUniformizationX q u = (u : K) / (1 - (u : K)) ^ 2 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n := by
  have h := (hasSum_tateUniformizationX_sub_of_norm_eq_one q u hq hu).tsum_eq
  linear_combination -h

/-- On the unit circle, the second Tate coordinate is a convergent `q`-expansion with finite
Laurent-polynomial coefficients. Its constant term is `u² / (1 - u)³`; the binomial coefficients
are integers before specialization, so the formula also applies in characteristics two and three. -/
theorem hasSum_tateUniformizationY_sub_of_norm_eq_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n)
      (tateUniformizationY q u - (u : K) ^ 2 / (1 - (u : K)) ^ 3) := by
  have hui : ‖(u : K)⁻¹‖ = 1 := by simp [hu]
  have hp := (hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (C := 1) (k := 0)
    (fun d ↦ (d.choose 2 : K) * (u : K) ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using
        IsUltrametricDist.norm_natCast_le_one K (d.choose 2)) hq).summable
  have hm := (hasSum_sum_divisors_mul_pow_of_norm_le_mul_pow (C := 1) (k := 0)
    (fun d ↦ -((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d) (fun d ↦ by
      simpa [norm_mul, norm_pow, hu] using
        IsUltrametricDist.norm_natCast_le_one K ((d + 1).choose 2)) hq).summable
  have hs := summable_divisorSumSeries (K := K) 1 hq
  suffices h : HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n)
      ((∑' n : ℕ, (∑ d ∈ n.divisors, (d.choose 2 : K) * (u : K) ^ d) * (q : K) ^ n) +
      (∑' n : ℕ, (∑ d ∈ n.divisors, -((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d) *
        (q : K) ^ n) + divisorSumAt 1 (q : K)) by
    convert h using 1
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
    simp_rw [hneg, ← tsum_choose_two_mul_pow_succ _ (norm_pow_pnat_mul_lt_one hq hu _),
      ← tsum_neg_choose_two_mul_pow_succ _ (norm_pow_pnat_mul_lt_one hq hui _)]
    have he := tsum_tsum_mul_pow_eq_tsum_sum_divisors_of_norm_le_mul_pow (C := 1) (k := 0)
      (fun d ↦ (d.choose 2 : K))
      (fun d ↦ by simpa using IsUltrametricDist.norm_natCast_le_one K (d.choose 2)) hq hu.le
    have hei := tsum_tsum_mul_pow_eq_tsum_sum_divisors_of_norm_le_mul_pow (C := 1) (k := 0)
      (fun d ↦ -((d + 1).choose 2 : K))
      (fun d ↦ by simpa using IsUltrametricDist.norm_natCast_le_one K ((d + 1).choose 2)) hq hui.le
    rw [he, hei]
    simp only [zpow_zero, one_mul]
    ring
  convert (hp.hasSum.add hm.hasSum).add hs.hasSum using 1
  · funext n
    simp only [sigma_one_apply]
    push_cast
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · simp only [divisorSumAt_def]

/-- The second Tate coordinate equals its unit-circle divisor-sum expansion.
Convergence is given by `hasSum_tateUniformizationY_sub_of_norm_eq_one`. -/
theorem tateUniformizationY_eq_add_tsum_sum_divisors_of_norm_eq_one
    (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu : ‖(u : K)‖ = 1) :
    tateUniformizationY q u = (u : K) ^ 2 / (1 - (u : K)) ^ 3 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n := by
  have h := (hasSum_tateUniformizationY_sub_of_norm_eq_one q u hq hu).tsum_eq
  linear_combination -h

end TauCeti

end
