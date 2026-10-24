/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
* `TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet`: a measure with an exponential moment at
  `0` is finite.
* `TauCeti.mgf_lt_one_of_nonneg_of_neg`: under a probability measure, the moment-generating
  function of a nonnegative random variable that is not almost surely zero is strictly less than
  `1` at every negative argument.
* `TauCeti.mgf_id_conv`: the moment-generating function of a convolution of two s-finite measures
  on `ℝ` is the product of their moment-generating functions.  This is the transform side of
  `MeasureTheory.Measure.conv`, the companion of `MeasureTheory.charFun_conv`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- A measure is a probability measure if the moment-generating function of any real-valued
statistic equals `1` at zero. -/
theorem isProbabilityMeasure_of_mgf_zero_eq_one (hmgf : mgf X μ 0 = 1) :
    IsProbabilityMeasure μ := by
  rw [mgf_zero'] at hmgf
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 hmgf⟩

/-- A measure admitting an exponential moment at rate `0` is finite: at rate `0` the integrand is
the constant `1`, whose integrability is finiteness of the measure. -/
theorem isFiniteMeasure_of_zero_mem_integrableExpSet (h : (0 : ℝ) ∈ integrableExpSet X μ) :
    IsFiniteMeasure μ :=
  (integrable_const_iff_isFiniteMeasure one_ne_zero).mp <| by
    simpa using integrable_of_mem_integrableExpSet h

/-- Under a probability measure, the moment-generating function of an almost surely nonnegative
random variable that is positive with positive probability is strictly less than `1` at every
negative argument. -/
theorem mgf_lt_one_of_nonneg_of_neg [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    (hX0 : 0 ≤ᵐ[μ] X) (hpos : μ {ω | 0 < X ω} ≠ 0) {t : ℝ} (ht : t < 0) : mgf X μ t < 1 := by
  have hle : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 := by
    filter_upwards [hX0] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ht.le hω)
  have hint : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
    Integrable.of_bound (by fun_prop) 1 <| hle.mono fun ω hω ↦ by
      rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  -- `1 - exp (t * X)` is nonnegative and vanishes exactly where `X` does.
  have hdiff : 0 < ∫ ω, (1 - Real.exp (t * X ω)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hle.mono fun ω hω ↦ sub_nonneg.2 hω)
      ((integrable_const 1).sub hint)]
    refine pos_iff_ne_zero.2 fun h0 ↦ hpos <| measure_mono_null (fun ω hω ↦ ?_) h0
    have : t * X ω < 0 := mul_neg_of_neg_of_pos ht hω
    simp [Function.mem_support, sub_eq_zero, (Real.exp_lt_one_iff.2 this).ne']
  rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul] at hdiff
  rw [mgf]
  linarith

/-- **The moment-generating function of a convolution is the product of the two
moment-generating functions.** This is the transform companion of `MeasureTheory.charFun_conv`.
No integrability hypothesis is needed, even though Mathlib totalizes a divergent `mgf` to `0`. -/
@[simp]
theorem mgf_id_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] :
    mgf id (μ ∗ ν) = mgf id μ * mgf id ν := by
  ext t
  rw [Measure.conv, mgf_id_map (by fun_prop), mgf]
  simp only [mul_add, Real.exp_add]
  exact integral_prod_mul (L := ℝ) (fun x ↦ Real.exp (t * x)) fun y ↦ Real.exp (t * y)

end TauCeti
