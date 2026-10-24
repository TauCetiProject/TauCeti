/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.AsymmetricLaplace.Transforms

/-!
# Natural moments of asymmetric Laplace laws

Every natural power, including powers about an arbitrary real point, is integrable against an
asymmetric Laplace law. The moments about its location parameter are finite binomial sums of
independent exponential moments. A second binomial expansion supplies every raw moment.
The location parameter need not equal the mean when the two rates differ.

The formulas include order zero. Integrability also holds for invalid rates, when the law is zero.
The construction and exponential moment API are in `AsymmetricLaplace.Basic` and
`AsymmetricLaplace.Transforms`.

## Reference

* S. Kotz, T. J. Kozubowski, K. Podgórski, *The Laplace Distribution and Generalizations*,
  Birkhäuser (2001), ch. 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped NNReal

namespace TauCeti.Probability

variable {m l r : ℝ}

/-- Every natural power about any real point is integrable, including at invalid rates. -/
theorem integrable_pow_sub_asymmetricLaplaceMeasure (m l r c : ℝ) (n : ℕ) :
    Integrable (fun x ↦ (x - c) ^ n) (asymmetricLaplaceMeasure m l r) := by
  by_cases hl : 0 < l
  · by_cases hr : 0 < r
    · have := isProbabilityMeasure_asymmetricLaplaceMeasure hl hr m
      have hzero : 0 ∈ interior (integrableExpSet id (asymmetricLaplaceMeasure m l r)) := by
        rw [integrableExpSet_id_asymmetricLaplaceMeasure hl hr, interior_Ioo]
        exact ⟨neg_neg_of_pos hl, hr⟩
      have hmem := (memLp_of_mem_interior_integrableExpSet hzero (n : ℝ≥0)).sub (memLp_const c)
      apply (integrable_norm_iff (by fun_prop)).mp
      simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_pow] using
        hmem.integrable_norm_pow'
    · simp [asymmetricLaplaceMeasure_of_nonpos_right (not_lt.mp hr)]
  · simp [asymmetricLaplaceMeasure_of_nonpos_left (not_lt.mp hl)]

/-- Every natural raw moment of an asymmetric Laplace law is integrable, for all parameters. -/
theorem integrable_pow_asymmetricLaplaceMeasure (m l r : ℝ) (n : ℕ) :
    Integrable (fun x ↦ x ^ n) (asymmetricLaplaceMeasure m l r) := by
  simpa only [sub_zero] using integrable_pow_sub_asymmetricLaplaceMeasure m l r 0 n

/-- Moments about the location are binomial expansions of the independent exponential moments.
These are moments about `m`, which need not be the mean. -/
theorem integral_pow_sub_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m : ℝ) (n : ℕ) :
    ∫ x, (x - m) ^ n ∂asymmetricLaplaceMeasure m l r =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        ((k.factorial : ℝ) / r ^ k) *
        ((-1 : ℝ) ^ (n - k) * ((n - k).factorial : ℝ) / l ^ (n - k)) := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have hnegpow (k : ℕ) : (fun y : ℝ ↦ (-y) ^ k) = fun y ↦ (-1 : ℝ) ^ k * y ^ k :=
    funext fun y ↦ neg_pow y k
  have hterm (k : ℕ) : Integrable
      (fun z : ℝ × ℝ ↦ z.1 ^ k * (-z.2) ^ (n - k) * (n.choose k : ℝ))
      ((expMeasure r).prod (expMeasure l)) := by
    have hneg : Integrable (fun y : ℝ ↦ (-y) ^ (n - k)) (expMeasure l) := by
      rw [hnegpow]
      exact (integrable_pow_expMeasure hl (n - k)).const_mul _
    exact ((integrable_pow_expMeasure hr k).mul_prod hneg).mul_const _
  rw [asymmetricLaplaceMeasure_of_pos hl hr, integral_map (by fun_prop) (by fun_prop)]
  have hcenter (z : ℝ × ℝ) : m + z.1 - z.2 - m = z.1 - z.2 := by ring
  simp_rw [hcenter]
  simp_rw [sub_eq_add_neg, add_pow]
  rw [integral_finsetSum _ (fun k _ ↦ hterm k)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_mul_const,
    integral_prod_mul (fun x : ℝ ↦ x ^ k) (fun y : ℝ ↦ (-y) ^ (n - k)),
    integral_pow_expMeasure hr, hnegpow, integral_const_mul, integral_pow_expMeasure hl]
  ring

/-- All natural raw moments are finite binomial sums. The inner sum computes moments about the
location from the right and left exponential variables; the outer sum restores the location. -/
theorem integral_pow_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) (m : ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂asymmetricLaplaceMeasure m l r =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * m ^ (n - k) *
        (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
          ((j.factorial : ℝ) / r ^ j) *
          ((-1 : ℝ) ^ (k - j) * ((k - j).factorial : ℝ) / l ^ (k - j))) := by
  have hexpand (x : ℝ) : x ^ n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * m ^ (n - k) * (x - m) ^ k := by
    calc
      x ^ n = ((x - m) + m) ^ n := by congr 1; ring
      _ = _ := by
        rw [add_pow]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun k _ ↦
    (integrable_pow_sub_asymmetricLaplaceMeasure m l r m k).const_mul _)]
  simp_rw [integral_const_mul, integral_pow_sub_asymmetricLaplaceMeasure hl hr]

end TauCeti.Probability
