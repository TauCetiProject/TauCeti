/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Kumaraswamy.Basic
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# Moments of the Kumaraswamy distribution

For positive shape parameters `a` and `b`, the real power `x ^ q` is integrable against the
Kumaraswamy `(a, b)` law exactly when `-a < q`, and then its integral is
`b * beta (1 + q / a) b`. Both facts transfer from the real-power moments of the Beta `(1, b)`
law through the identity `x ^ q = (x ^ a) ^ (q / a)`, since `x ^ a` is Beta `(1, b)`
distributed. The natural moments, the mean and the variance are special cases. The law is carried
by the unit interval, so every exponential moment exists.

## Main results

* `TauCeti.Probability.integrable_rpow_kumaraswamyMeasure_iff` — the sharp integrability
  threshold `-a < q` for real powers;
* `TauCeti.Probability.integral_rpow_kumaraswamyMeasure` — the real-power moment
  `b * beta (1 + q / a) b`;
* `TauCeti.Probability.integral_id_kumaraswamyMeasure` and
  `TauCeti.Probability.variance_id_kumaraswamyMeasure` — the mean and variance;
* `TauCeti.Probability.integrableExpSet_id_kumaraswamyMeasure` — every exponential moment
  exists.

## References

* M. C. Jones, *Kumaraswamy's distribution: A beta-type distribution with some tractability
  advantages*, Statistical Methodology 6 (2009), 70–81.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {a b q : ℝ}

/-- Against a Kumaraswamy law, the power `x ^ q` is almost everywhere the power `y ^ (q / a)` of
the Beta-distributed variable `y = x ^ a`, written in the mixed-power form of the Beta moment
API. -/
private theorem rpow_ae_eq_comp_rpow (ha : 0 < a) (b q : ℝ) :
    (fun x : ℝ ↦ x ^ q) =ᵐ[kumaraswamyMeasure a b]
      (fun y : ℝ ↦ y ^ (q / a) * (1 - y) ^ (0 : ℝ)) ∘ fun x ↦ x ^ a := by
  filter_upwards [ae_mem_Ioo_kumaraswamyMeasure a b] with x hx
  rw [Function.comp_apply, Real.rpow_zero, mul_one, ← Real.rpow_mul hx.1.le,
    mul_div_cancel₀ q ha.ne']

/-- The Beta exponent `1 + q / a` of the pushed-forward moment is positive exactly above the
threshold `-a`. -/
private theorem zero_lt_one_add_div_iff (ha : 0 < a) : 0 < 1 + q / a ↔ -a < q := by
  rw [one_add_div ha.ne', div_pos_iff_of_pos_right ha]
  constructor <;> intro h <;> linarith

/-- The real power `x ^ q` is integrable against the Kumaraswamy `(a, b)` law exactly when
`-a < q`. -/
@[simp]
theorem integrable_rpow_kumaraswamyMeasure_iff (ha : 0 < a) (hb : 0 < b) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (kumaraswamyMeasure a b) ↔ -a < q := by
  rw [integrable_congr (rpow_ae_eq_comp_rpow ha b q), ← integrable_map_measure
    (by fun_prop : Measurable fun y : ℝ ↦ y ^ (q / a) * (1 - y) ^ (0 : ℝ)).aestronglyMeasurable
    (by fun_prop), map_rpow_kumaraswamyMeasure ha hb,
    integrable_rpow_mul_one_sub_rpow_betaMeasure_iff zero_lt_one hb, add_zero,
    zero_lt_one_add_div_iff ha]
  exact and_iff_left hb

/-- The real-power moment of a Kumaraswamy `(a, b)` variable above the threshold `-a`. -/
theorem integral_rpow_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) (hq : -a < q) :
    ∫ x, x ^ q ∂kumaraswamyMeasure a b = b * beta (1 + q / a) b := by
  have hg : Measurable fun y : ℝ ↦ y ^ (q / a) * (1 - y) ^ (0 : ℝ) := by fun_prop
  rw [integral_congr_ae (rpow_ae_eq_comp_rpow ha b q)]
  refine (integral_map (μ := kumaraswamyMeasure a b) (φ := fun x : ℝ ↦ x ^ a) (by fun_prop)
    hg.aestronglyMeasurable).symm.trans ?_
  rw [map_rpow_kumaraswamyMeasure ha hb, integral_rpow_mul_one_sub_rpow_betaMeasure zero_lt_one hb
      ((zero_lt_one_add_div_iff ha).mpr hq) (by rwa [add_zero]),
    add_zero, beta_comm 1 b, beta_one_right hb]
  field_simp

/-- Every natural power is integrable against a Kumaraswamy law. -/
theorem integrable_pow_kumaraswamyMeasure (a b : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (kumaraswamyMeasure a b) := by
  by_cases hab : 0 < a ∧ 0 < b
  swap
  · simp [kumaraswamyMeasure_of_not_pos hab]
  obtain ⟨ha, hb⟩ := hab
  simpa only [Real.rpow_natCast] using (integrable_rpow_kumaraswamyMeasure_iff ha hb n).mpr
    (lt_of_lt_of_le (neg_neg_of_pos ha) n.cast_nonneg)

/-- The `n`th raw moment of a Kumaraswamy `(a, b)` variable. -/
@[simp]
theorem integral_pow_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    ∫ x, x ^ n ∂kumaraswamyMeasure a b = b * beta (1 + n / a) b := by
  simpa only [Real.rpow_natCast] using integral_rpow_kumaraswamyMeasure (q := n) ha hb
    (lt_of_lt_of_le (neg_neg_of_pos ha) n.cast_nonneg)

/-- The mean of a Kumaraswamy `(a, b)` variable. -/
@[simp]
theorem integral_id_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x ∂kumaraswamyMeasure a b = b * beta (1 + 1 / a) b := by
  simpa using integral_pow_kumaraswamyMeasure ha hb 1

/-- The variance of a Kumaraswamy `(a, b)` variable. -/
@[simp]
theorem variance_id_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) :
    variance id (kumaraswamyMeasure a b) =
      b * beta (1 + 2 / a) b - (b * beta (1 + 1 / a) b) ^ 2 := by
  have := isProbabilityMeasure_kumaraswamyMeasure ha hb
  have hmem : MemLp id 2 (kumaraswamyMeasure a b) :=
    memLp_of_bounded (ae_mem_Icc_kumaraswamyMeasure a b) measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_pow_kumaraswamyMeasure ha hb 2,
    integral_id_kumaraswamyMeasure ha hb, Nat.cast_ofNat]

/-- Every exponential moment of a Kumaraswamy law exists. -/
@[simp]
theorem integrableExpSet_id_kumaraswamyMeasure (a b : ℝ) :
    integrableExpSet id (kumaraswamyMeasure a b) = univ := by
  by_cases hab : 0 < a ∧ 0 < b
  swap
  · simp [kumaraswamyMeasure_of_not_pos hab, integrableExpSet]
  have := isProbabilityMeasure_kumaraswamyMeasure hab.1 hab.2
  ext t
  simp only [mem_univ, iff_true, integrableExpSet, mem_ofPred_eq, id_eq]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_kumaraswamyMeasure a b)

end TauCeti.Probability
