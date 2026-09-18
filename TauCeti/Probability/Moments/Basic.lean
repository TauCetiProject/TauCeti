/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
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

/-- **The moment-generating function of a convolution is the product of the two
moment-generating functions.** A convolution is the image of the product measure under addition,
so the exponential moment factors over the two coordinates and Fubini
(`MeasureTheory.integral_prod_mul`) separates it.  This is the transform companion of
`MeasureTheory.charFun_conv`.

No integrability hypothesis is needed, even though Mathlib totalizes a divergent `mgf` to `0`:
`integral_prod_mul` is itself unconditional, and as soon as one of the two exponential moments
diverges both sides are `0`. -/
theorem mgf_id_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] :
    mgf id (μ ∗ ν) = mgf id μ * mgf id ν := by
  ext t
  rw [Measure.conv, mgf_id_map (by fun_prop), mgf]
  simp only [mul_add, Real.exp_add]
  exact integral_prod_mul (L := ℝ) (fun x ↦ Real.exp (t * x)) fun y ↦ Real.exp (t * y)

end TauCeti
