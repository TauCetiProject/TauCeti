/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Mixture.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of probability mixtures

The cdf of a probability mixture is the mixing integral of the component cdfs. Combining this
identity with the quantile--cdf adjunction characterizes its lower quantile without continuity or
atomlessness assumptions. For a finite mixture, the integral becomes the weighted sum of the
component cdfs given by `TauCeti.Probability.cdf_finiteMixtureMeasure`.

These are adjunction formulas rather than root characterizations: atoms and flat portions of a
mixture cdf can prevent an interior level from being attained uniquely.

## Main results

* `MeasureTheory.Measure.quantile_bind_le_iff` characterizes a general mixture quantile by the
  integral of its component cdfs.
* `TauCeti.Probability.quantile_finiteMixtureMeasure_le_iff` specializes the quantile adjunction
  to that finite sum.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory Set

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {A : Type*} [MeasurableSpace A]

/-- At an interior level, the quantile of a probability mixture is characterized by the integral
of the component cdfs. No continuity or atomlessness assumption is needed. -/
theorem quantile_bind_le_iff (rho : Measure A) [IsProbabilityMeasure rho]
    (K : A → Measure ℝ) (hK : AEMeasurable K rho)
    (hprob : ∀ᵐ a ∂rho, IsProbabilityMeasure (K a)) {u x : ℝ} (hu : u ∈ Ioo 0 1) :
    (rho.bind K).quantile u ≤ x ↔ u ≤ ∫ a, cdf (K a) x ∂rho := by
  let _ : IsProbabilityMeasure (rho.bind K) := isProbabilityMeasure_bind hK hprob
  rw [quantile_le_iff _ hu.1 hu.2, cdf_bind rho K hK hprob]

end MeasureTheory.Measure

namespace TauCeti.Probability

variable {I : Type*} [Fintype I] {p : StdSimplex NNReal I} {K : I → Measure ℝ} {u x : ℝ}

/-- At an interior level, the quantile of a finite probability mixture lies below `x` exactly
when the weighted sum of component cdfs at `x` reaches that level. Only the positive-weight
components need to be probability measures. -/
theorem quantile_finiteMixtureMeasure_le_iff
    (hK : ∀ i, 0 < p.weights i → IsProbabilityMeasure (K i)) (hu : u ∈ Ioo 0 1) :
    (finiteMixtureMeasure p K).quantile u ≤ x ↔
      u ≤ ∑ i, (p.weights i : ℝ) * cdf (K i) x := by
  rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_finiteMixtureMeasure hK]

end TauCeti.Probability
