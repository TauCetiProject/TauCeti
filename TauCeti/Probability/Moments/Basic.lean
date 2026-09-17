/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
* `TauCeti.mgf_id_conv`: the moment-generating function of a convolution of two probability
  measures on `ℝ` is the product of their moment-generating functions.  This is the transform
  side of `MeasureTheory.Measure.conv`, the companion of `MeasureTheory.charFun_conv`.
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
moment-generating functions.** A convolution is the law of a sum of independent variables — the
image of the product measure under addition — so this is the independent-sum rule
`ProbabilityTheory.IndepFun.mgf_add` read on the two coordinate projections.

No integrability hypothesis is needed, even though Mathlib totalizes a divergent `mgf` to `0`.
The two exponential moments are independent and strictly positive, so their `ℝ≥0∞`-valued product
is finite exactly when both factors are: the left side diverges precisely when one of the right
side's factors does, and then both sides are `0`. -/
theorem mgf_id_conv {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    mgf id (μ ∗ ν) = mgf id μ * mgf id ν := by
  ext t
  rw [Measure.conv, mgf_id_map (by fun_prop)]
  -- `mgf_id_map` leaves addition under a lambda, while `IndepFun.mgf_add'` expects the
  -- definitionally equal pointwise sum of the two projection functions.
  change mgf ((fun p : ℝ × ℝ ↦ p.1) + fun p ↦ p.2) (μ.prod ν) t =
    mgf id μ t * mgf id ν t
  rw [(indepFun_prod measurable_id measurable_id).mgf_add'
    (X := fun p : ℝ × ℝ ↦ p.1) (Y := fun p ↦ p.2)]
  · rw [← mgf_id_map (μ := μ.prod ν) measurable_fst.aemeasurable,
      ← mgf_id_map (μ := μ.prod ν) measurable_snd.aemeasurable]
    simp
  all_goals fun_prop

end TauCeti
