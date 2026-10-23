/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Coordinates
import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.LinearCombination

/-!
# Tate coordinate expansions on an annulus

Over any complete normed field, for multiplicative parameters satisfying `‖q * u‖ < 1` and
`‖q * u⁻¹‖ < 1`, the Tate coordinates have convergent expansions in `q`, with
Laurent-polynomial coefficients in `u`.
Their constant terms are the rational parametrization `u / (1 - u)²`, `u² / (1 - u)³`
of the nodal cubic. All remaining coefficients are finite divisor sums.

These expansions cover the boundary of the fundamental annulus, which is not covered by
geometric expansion in `u` and `q / u`: when `‖u‖ = 1`, the term at index zero must instead be
kept as a rational function. The unit-circle equation proof in
`TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Equation` uses these expansions to compare
the evaluated formal coordinates with the analytic coordinates. At `u = 1` the rational terms
retain the totalized field values.

## Main results

* `hasSum_tateUniformizationX_sub` and
  `hasSum_tateUniformizationY_sub` give convergence and values of the
  divisor-sum series after removing the rational constant terms.
* `tateUniformizationX_eq_add_tsum_sum_divisors` and
  `tateUniformizationY_eq_add_tsum_sum_divisors` give the corresponding
  coordinate identities.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, §V.3.
* J. Tate, *A review of non-Archimedean elliptic functions* (1995).
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace TauCeti

variable {K : Type*} [NormedField K] [CompleteSpace K]

omit [CompleteSpace K] in
private lemma norm_natCast_le_mul_pow_one (d : ℕ) : ‖(d : K)‖ ≤ 1 * (d : ℝ) ^ 1 := by
  simpa using (Nat.norm_cast_le (α := K) d)

/-- On the annulus `‖q * u‖ < 1`, `‖q * u⁻¹‖ < 1`, the first Tate coordinate has a convergent
`q`-expansion with finite Laurent-polynomial coefficients. Its constant term is `u / (1 - u)²`. -/
theorem hasSum_tateUniformizationX_sub (q u : Kˣ)
    (hqu : ‖(q : K) * (u : K)‖ < 1) (hqui : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n)
      (tateUniformizationX q u - (u : K) / (1 - (u : K)) ^ 2) := by
  have hq := norm_lt_one_of_norm_mul_lt_one_of_norm_mul_inv_lt_one u hqu hqui
  have hp := hasSum_sum_divisors_mul_pow_mul_of_tsum_eq (fun d ↦ (d : K))
    norm_natCast_le_mul_pow_one hq hqu _ tsum_natCast_succ_mul_pow_succ
  have hm := hasSum_sum_divisors_mul_pow_mul_of_tsum_eq (fun d ↦ (d : K))
    norm_natCast_le_mul_pow_one hq hqui _ tsum_natCast_succ_mul_pow_succ
  have hs := (hasSum_sum_divisors_mul_pow norm_natCast_le_mul_pow_one hq).summable.hasSum
  convert (hp.add hm).sub (hs.mul_left 2) using 1
  · funext n
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · rw [tateUniformizationX_eq_tsum_nat q hq u]
    simp only [divisorSumAt_def, sigma_one_apply]
    push_cast
    ring

/-- The first Tate coordinate equals its divisor-sum expansion on the annulus.
Convergence is given by `hasSum_tateUniformizationX_sub`. -/
theorem tateUniformizationX_eq_add_tsum_sum_divisors
    (q u : Kˣ)
    (hqu : ‖(q : K) * (u : K)‖ < 1) (hqui : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    tateUniformizationX q u = (u : K) / (1 - (u : K)) ^ 2 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        (d : K) * ((u : K) ^ d + (u : K)⁻¹ ^ d - 2)) * (q : K) ^ n := by
  have h := (hasSum_tateUniformizationX_sub q u hqu hqui).tsum_eq
  linear_combination -h

/-- On the annulus `‖q * u‖ < 1`, `‖q * u⁻¹‖ < 1`, the second Tate coordinate has a convergent
`q`-expansion with finite Laurent-polynomial coefficients. Its constant term is `u² / (1 - u)³`;
the binomial coefficients
are integers before specialization, so the formula also applies in characteristics two and three. -/
theorem hasSum_tateUniformizationY_sub (q u : Kˣ)
    (hqu : ‖(q : K) * (u : K)‖ < 1) (hqui : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    HasSum (fun n : ℕ ↦ (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n)
      (tateUniformizationY q u - (u : K) ^ 2 / (1 - (u : K)) ^ 3) := by
  have hq := norm_lt_one_of_norm_mul_lt_one_of_norm_mul_inv_lt_one u hqu hqui
  have hp (d : ℕ) : ‖(d.choose 2 : K)‖ ≤ 1 * (d : ℝ) ^ 2 := by
    calc
      _ ≤ (d.choose 2 : ℝ) := by simpa using (Nat.norm_cast_le (α := K) (d.choose 2))
      _ ≤ 1 * (d : ℝ) ^ 2 := by
        rw [one_mul]
        exact_mod_cast Nat.choose_le_pow d 2
  have hm (d : ℕ) : ‖-((d + 1).choose 2 : K)‖ ≤ 2 * (d : ℝ) ^ 2 := by
    rw [norm_neg]
    calc
      _ ≤ ((d + 1).choose 2 : ℝ) := by
        simpa using (Nat.norm_cast_le (α := K) ((d + 1).choose 2))
      _ ≤ 2 * (d : ℝ) ^ 2 := by
        rw [Nat.choose_succ_succ' d 1, Nat.choose_one_right, Nat.cast_add]
        have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by decide) d
        have hc : (d.choose 2 : ℝ) ≤ (d : ℝ) ^ 2 := by
          exact_mod_cast Nat.choose_le_pow d 2
        linarith
  have hp := hasSum_sum_divisors_mul_pow_mul_of_tsum_eq (fun d ↦ (d.choose 2 : K))
    hp hq hqu _ tsum_choose_two_mul_pow_succ
  have hm := hasSum_sum_divisors_mul_pow_mul_of_tsum_eq (fun d ↦ -((d + 1).choose 2 : K))
    hm hq hqui _ tsum_neg_choose_two_mul_pow_succ
  have hs := (hasSum_sum_divisors_mul_pow norm_natCast_le_mul_pow_one hq).summable.hasSum
  convert (hp.add hm).add hs using 1
  · funext n
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  · rw [tateUniformizationY_eq_tsum_nat q hq u]
    simp only [divisorSumAt_def, sigma_one_apply]
    push_cast
    ring

/-- The second Tate coordinate equals its divisor-sum expansion on the annulus.
Convergence is given by `hasSum_tateUniformizationY_sub`. -/
theorem tateUniformizationY_eq_add_tsum_sum_divisors
    (q u : Kˣ)
    (hqu : ‖(q : K) * (u : K)‖ < 1) (hqui : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    tateUniformizationY q u = (u : K) ^ 2 / (1 - (u : K)) ^ 3 +
      ∑' n : ℕ, (∑ d ∈ n.divisors,
        ((d.choose 2 : K) * (u : K) ^ d - ((d + 1).choose 2 : K) * (u : K)⁻¹ ^ d +
          (d : K))) *
          (q : K) ^ n := by
  have h := (hasSum_tateUniformizationY_sub q u hqu hqui).tsum_eq
  linear_combination -h

end TauCeti

end
