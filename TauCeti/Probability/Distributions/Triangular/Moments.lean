/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Triangular.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Moments of the triangular distribution

For endpoints `a < b` and mode `a ≤ c ≤ b`, the triangular law is carried by the compact interval
`[a, b]`, so every natural power and every exponential is integrable against it. Its density is
linear on each of the two branches `(a, c)` and `(c, b)`, so an integral against the law splits
into two interval integrals of a linear weight against the integrand
(`integral_triangularMeasure_eq_intervalIntegral`). Expanding `x ^ n` binomially about the
outer endpoint of each branch gives the natural moments as a finite sum,

`E[X ^ n] = 2 / (b - a) * ∑ k ∈ range (n + 1),
  n.choose k / (k + 2) * (a ^ (n - k) * (c - a) ^ (k + 1) - b ^ (n - k) * (c - b) ^ (k + 1))`,

whose two halves are the contributions of the rising and the falling branch. The formula holds
uniformly when the mode is an endpoint: the contribution of the empty branch vanishes. The mean
`(a + b + c) / 3` is the case `n = 1`, and the variance
`(a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) / 18` follows from the cases `n = 1, 2`.

## Main results

* `TauCeti.Probability.integral_triangularMeasure_eq_intervalIntegral` — integration of an
  integrable function against the law as the sum of its two branch integrals;
* `TauCeti.Probability.integral_pow_triangularMeasure` — the natural moments;
* `TauCeti.Probability.integral_id_triangularMeasure` and
  `TauCeti.Probability.variance_id_triangularMeasure` — the mean and the variance;
* `TauCeti.Probability.integrableExpSet_id_triangularMeasure` — every exponential moment exists.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 26, Section 9.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

variable {a b c : ℝ}

/-- Every exponential moment of a triangular law exists, for all parameter values. -/
@[simp]
theorem integrableExpSet_id_triangularMeasure (a b c : ℝ) :
    integrableExpSet id (triangularMeasure a b c) = univ := by
  by_cases h : a < b ∧ a ≤ c ∧ c ≤ b
  · have := isProbabilityMeasure_triangularMeasure h.1 h.2.1 h.2.2
    ext t
    simp only [mem_univ, iff_true, integrableExpSet, mem_ofPred_eq, id_eq]
    exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
      (ae_mem_Icc_triangularMeasure a b c)
  · simp [triangularMeasure_eq_zero_of_not h, integrableExpSet]

/-- Every natural power is integrable against a triangular law, for all parameter values. -/
@[simp]
theorem integrable_pow_triangularMeasure (a b c : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (triangularMeasure a b c) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp only [integrableExpSet_id_triangularMeasure, interior_univ, mem_univ]

/-- **Branch decomposition.** When the mode lies between the endpoints, integrating an integrable
function against the triangular law is integrating it against the linear weight of the rising
branch over `[a, c]` plus against that of the falling branch over `[c, b]`. -/
theorem integral_triangularMeasure_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hac : a ≤ c) (hcb : c ≤ b) {g : ℝ → E}
    (hg : Integrable g (triangularMeasure a b c)) :
    ∫ x, g x ∂triangularMeasure a b c =
      (∫ x in a..c, (2 * (x - a) / ((b - a) * (c - a))) • g x) +
        ∫ x in c..b, (2 * (b - x) / ((b - a) * (b - c))) • g x := by
  set F : ℝ → E := fun x ↦ triangularPDFReal a b c x • g x with hF
  have hsupp : Function.support F ⊆ Icc a b := fun x hx ↦ by
    by_contra h
    exact hx (by simp only [hF, triangularPDFReal_of_notMem_Ioo
      (fun h' ↦ h (Ioo_subset_Icc_self h')), zero_smul])
  have hFint : Integrable F := integrable_triangularMeasure_iff.1 hg
  rw [integral_triangularMeasure_eq, ← hF,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      Function.notMem_support.1 fun h ↦ hx (hsupp h),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hac.trans hcb),
    ← intervalIntegral.integral_add_adjacent_intervals (hFint.intervalIntegrable (b := c))
      hFint.intervalIntegrable]
  congr 1
  · -- On the rising branch the density is the rising linear weight, except at the mode.
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [volume.ae_ne c] with x hxc hx
    rw [uIoc_of_le hac] at hx
    simp only [hF, triangularPDFReal_of_mem_Ioo_left hcb ⟨hx.1, hx.2.lt_of_ne hxc⟩]
  · -- On the falling branch the density is the falling linear weight, except at `b`.
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [volume.ae_ne b] with x hxb hx
    rw [uIoc_of_le hcb] at hx
    simp only [hF, triangularPDFReal_of_mem_Ico_right hac (hac.trans_lt hx.1)
      ⟨hx.1.le, hx.2.lt_of_ne hxb⟩]

/-- **Natural moments.** The `n`th raw moment of the triangular law with mode `a ≤ c ≤ b`, as the
sum of the binomial expansions of the rising branch about `a` and of the falling branch about `b`.
In the degenerate case `a = b = c` the law is zero and so is the right-hand side. -/
theorem integral_pow_triangularMeasure (hac : a ≤ c) (hcb : c ≤ b) (n : ℕ) :
    ∫ x, x ^ n ∂triangularMeasure a b c =
      2 / (b - a) * ∑ k ∈ range (n + 1), (n.choose k : ℝ) / (k + 2) *
        (a ^ (n - k) * (c - a) ^ (k + 1) - b ^ (n - k) * (c - b) ^ (k + 1)) := by
  rw [integral_triangularMeasure_eq_intervalIntegral hac hcb
    (integrable_pow_triangularMeasure a b c n)]
  simp only [smul_eq_mul]
  have hrise : ∫ x in a..c, 2 * (x - a) / ((b - a) * (c - a)) * x ^ n =
      2 / (b - a) * (1 / (c - a)) * ∫ x in a..c, x ^ n * (x - a) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1 with x
    rw [div_mul_eq_div_mul_one_div]
    ring
  have hfall : ∫ x in c..b, 2 * (b - x) / ((b - a) * (b - c)) * x ^ n =
      2 / (b - a) * (1 / (b - c)) * ∫ x in b..c, x ^ n * (x - b) := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_neg]
    congr 1 with x
    rw [div_mul_eq_div_mul_one_div]
    ring
  rw [hrise, hfall, integral_pow_mul_sub, integral_pow_mul_sub, mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun k _ ↦ ?_
  -- Each branch contributes `(mode - outer) ^ (k + 2) / (mode - outer)`, which is
  -- `(mode - outer) ^ (k + 1)` also when the branch is empty.
  have h1 : 1 / (c - a) * (c - a) ^ (k + 2) = (c - a) ^ (k + 1) := by
    rcases eq_or_ne (c - a) 0 with h | h
    · simp [h]
    · field_simp
      ring
  have h2 : 1 / (b - c) * (c - b) ^ (k + 2) = -(c - b) ^ (k + 1) := by
    rcases eq_or_ne (b - c) 0 with h | h
    · simp [show c - b = 0 by linarith]
    · rw [show c - b = -(b - c) by ring]
      field_simp
      ring
  linear_combination (2 / (b - a) * ((n.choose k : ℝ) / (k + 2)) * a ^ (n - k)) * h1 +
    (2 / (b - a) * ((n.choose k : ℝ) / (k + 2)) * b ^ (n - k)) * h2

/-- **Mean.** The mean of the triangular law with endpoints `a < b` and mode `a ≤ c ≤ b` is
`(a + b + c) / 3`. -/
@[simp]
theorem integral_id_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x, x ∂triangularMeasure a b c = (a + b + c) / 3 := by
  have h := integral_pow_triangularMeasure hac hcb 1
  simp only [pow_one, sum_range_succ, sum_range_zero] at h
  rw [h]
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp
  norm_num
  ring

/-- **Second moment.** The second raw moment of the triangular law with endpoints `a < b` and mode
`a ≤ c ≤ b` is `(a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c) / 6`. -/
@[simp]
theorem integral_sq_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x, x ^ 2 ∂triangularMeasure a b c =
      (a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c) / 6 := by
  rw [integral_pow_triangularMeasure hac hcb 2]
  simp only [sum_range_succ, sum_range_zero]
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  field_simp
  norm_num
  ring

/-- **Variance.** The variance of the triangular law with endpoints `a < b` and mode
`a ≤ c ≤ b` is `(a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) / 18`. -/
@[simp]
theorem variance_id_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) :
    variance id (triangularMeasure a b c) =
      (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) / 18 := by
  have := isProbabilityMeasure_triangularMeasure hab hac hcb
  have hmem : MemLp id 2 (triangularMeasure a b c) :=
    memLp_of_bounded (ae_mem_Icc_triangularMeasure a b c) measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_sq_triangularMeasure hab hac hcb,
    integral_id_triangularMeasure hab hac hcb]
  ring

end TauCeti.Probability
