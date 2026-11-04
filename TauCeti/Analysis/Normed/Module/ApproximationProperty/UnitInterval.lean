/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.MeasureTheory.Constructions.UnitInterval.Dyadic

/-!
# Metric approximation of `Lᵖ` spaces on the unit interval

For `1 ≤ p < ∞` and every finite measure `μ` on the unit interval `I`, the space `Lp E p μ` with
values in a finite-dimensional real or complex normed space `E` has the metric approximation
property. In particular this holds for the scalar spaces `Lᵖ([0, 1])` of Lebesgue measure. The
dyadic averaging operators `TauCeti.unitInterval.dyadicAverage` are finite-rank contractions that
converge pointwise to the identity, so they give uniform approximation on compact sets.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1.
* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
-/

public section

open MeasureTheory Filter
open scoped ENNReal NNReal unitInterval

namespace TauCeti

variable {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {μ : Measure I} [IsFiniteMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `1 ≤ p < ∞`, the space `Lp E p μ` of a finite measure `μ` on the unit interval, with
values in a finite-dimensional normed space `E`, has the metric approximation property. -/
theorem hasMetricApproximationProperty_Lp_unitInterval (hp : p ≠ ∞) :
    HasMetricApproximationProperty 𝕜 (Lp E p μ) :=
  have := FiniteDimensional.complete 𝕜 E
  hasMetricApproximationProperty_iff.2 <|
    HasBoundedApproximationPropertyWith.of_tendsto (l := atTop) (C := 1)
      (fun N => (unitInterval.dyadicAverage 𝕜 μ N : Lp E p μ →L[𝕜] Lp E p μ))
      unitInterval.hasFiniteRange_dyadicAverage
      (fun N => (unitInterval.norm_dyadicAverage_le N).trans_eq NNReal.coe_one.symm)
      (unitInterval.tendsto_dyadicAverage hp)

end TauCeti
