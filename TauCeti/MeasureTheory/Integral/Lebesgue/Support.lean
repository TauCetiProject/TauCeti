/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Positive integrals and non-concentration at zero

A probability law on the nonnegative half-line with positive extended mean gives
mass strictly less than one to zero. This supplies nondegeneracy from a positive
or infinite mean without assumptions on the law away from zero.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- A probability law on the half-line with positive extended mean is not concentrated
at zero. In particular, this applies to laws of infinite mean. -/
theorem measure_singleton_zero_lt_one_of_lintegral_pos
    (hmean : 0 < ∫⁻ u, (u : ℝ≥0∞) ∂μ) : μ {0} < 1 := by
  have hpos := (lintegral_pos_iff_support measurable_coe_nnreal_ennreal).1 hmean
  simpa [Function.support] using prob_compl_lt_one_sub_of_lt_prob hpos
    (measurableSet_support measurable_coe_nnreal_ennreal)

end MeasureTheory.Measure
