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
