/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.Analysis.SpecialFunctions.Exp.Negative

/-!
# Lebesgue integral bounds for negative exponentials

Because `ENNReal.expNeg` takes values in `[0, 1]`, integrating `(ENNReal.expNeg (f x) : ℝ≥0∞)`
against an arbitrary measure `μ` is bounded by `μ Set.univ`, and against a zero or probability
measure is bounded by `1`, with no measurability assumption on `f`.

## Main statements

* `TauCeti.lintegral_coe_expNeg_le`: `∫⁻ x, (ENNReal.expNeg (f x) : ℝ≥0∞) ∂μ ≤ μ Set.univ`.
* `TauCeti.lintegral_coe_expNeg_le_one`: `∫⁻ x, (ENNReal.expNeg (f x) : ℝ≥0∞) ∂μ ≤ 1` when `μ` is a
  zero or probability measure.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrating a negative exponential against any measure is bounded by total mass, with no
measurability or finiteness hypothesis. -/
theorem lintegral_coe_expNeg_le (f : α → ℝ≥0∞) :
    ∫⁻ x, (ENNReal.expNeg (f x) : ℝ≥0∞) ∂μ ≤ μ Set.univ :=
  (lintegral_mono fun _ ↦ ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)).trans_eq (by simp)

/-- Integrating a negative exponential against a zero or probability measure gives at most one,
with no measurability hypothesis on the integrand. -/
theorem lintegral_coe_expNeg_le_one [IsZeroOrProbabilityMeasure μ] (f : α → ℝ≥0∞) :
    ∫⁻ x, (ENNReal.expNeg (f x) : ℝ≥0∞) ∂μ ≤ 1 :=
  (lintegral_coe_expNeg_le f).trans prob_le_one

end TauCeti
