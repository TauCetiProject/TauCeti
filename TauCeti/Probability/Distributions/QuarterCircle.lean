/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Semicircle.LocationScale
public import TauCeti.Probability.Distributions.Semicircle.Moments

/-!
# The quarter-circle law

The quarter-circle law is the law of `|X|` for `X` distributed as the semicircle law of variance
one, which is supported on `[-2, 2]`. It has density `π⁻¹ √(4 - s²)` on `[0, 2]`.

## Main definitions

* `TauCeti.Probability.quarterCircle`: the image of `semicircleReal 0 1` under `x ↦ |x|`.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_quarterCircle`: total mass one.
* `TauCeti.Probability.quarterCircle_eq_withDensity`: the density `π⁻¹ √(4 - s²)` on `(0, ∞)`.
* `TauCeti.Probability.ae_mem_Icc_quarterCircle`: the law is carried by `[0, 2]`.
* `TauCeti.Probability.integral_pow_two_mul_quarterCircle`: even moments agree with those of the
  semicircle law.
* `TauCeti.Probability.integral_sq_quarterCircle`: the second moment is one.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The quarter-circle law: the law of `|X|` for `X` a semicircle variable of variance one. -/
def quarterCircle : Measure ℝ := (semicircleReal 0 1).map fun x ↦ |x|

theorem quarterCircle_def : quarterCircle = (semicircleReal 0 1).map fun x ↦ |x| := (rfl)

/-- The quarter-circle law is a probability measure. -/
instance isProbabilityMeasure_quarterCircle : IsProbabilityMeasure quarterCircle :=
  ⟨by rw [quarterCircle_def, Measure.map_apply (continuous_abs.measurable) MeasurableSet.univ]
      simp⟩

/-- The quarter-circle law has density `π⁻¹ √(4 - s²)` on the positive half-line. -/
theorem quarterCircle_eq_withDensity :
    quarterCircle = volume.withDensity
      ((Ioi 0).indicator fun s : ℝ ↦ ENNReal.ofReal (Real.pi⁻¹ * Real.sqrt (4 - s ^ 2))) := by
  rw [quarterCircle_def, semicircleReal_eq_withDensity 0 one_pos,
    map_abs_withDensity (by fun_prop)]
  congr 1
  ext s
  by_cases hs : s ∈ Ioi 0
  · simp only [indicator_of_mem hs, NNReal.coe_one, mul_one, sub_zero, neg_sq]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  · simp [indicator_of_notMem hs]

/-- The quarter-circle law is carried by `[0, 2]`. -/
theorem ae_mem_Icc_quarterCircle : ∀ᵐ s ∂quarterCircle, s ∈ Icc (0 : ℝ) 2 := by
  rw [quarterCircle_def]
  refine (ae_map_iff (continuous_abs.measurable.aemeasurable) measurableSet_Icc).2 ?_
  filter_upwards [ae_mem_Icc_semicircleReal 0 1] with x hx
  simp only [NNReal.coe_one, Real.sqrt_one, mul_one, zero_sub, zero_add, mem_Icc] at hx
  exact ⟨abs_nonneg x, abs_le.2 hx⟩

/-- The `2k`th moment of the quarter-circle law is the Catalan number `catalan k`. -/
@[simp]
theorem integral_pow_two_mul_quarterCircle (k : ℕ) :
    ∫ s, s ^ (2 * k) ∂quarterCircle = catalan k := by
  rw [quarterCircle_def, integral_map continuous_abs.measurable.aemeasurable (by fun_prop)]
  calc
    ∫ x, |x| ^ (2 * k) ∂semicircleReal 0 1 =
        ∫ x, x ^ (2 * k) ∂semicircleReal 0 1 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (even_two_mul k).pow_abs x)
    _ = catalan k := by rw [integral_pow_two_mul_semicircleReal_zero]; norm_num

/-- The second moment of the quarter-circle law is one. -/
@[simp]
theorem integral_sq_quarterCircle : ∫ s, s ^ 2 ∂quarterCircle = 1 := by
  simpa using integral_pow_two_mul_quarterCircle 1

end TauCeti.Probability
