/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Count
public import TauCeti.Probability.Process.Poisson.StrongLaw

/-!
# The long-run intensity of homogeneous temporal Poisson measures

The cumulative natural count on `(0,t]`, divided by `t`, converges almost surely to
the intensity of a homogeneous temporal Poisson random measure. The limit holds
along all nonnegative real times on a common full-measure event, including at rate
zero. The count representative, including its exceptional values, is the same as
in the temporal count API; no extra assumptions on the realizations are needed.

This connects the random-measure description to the strong law obtained from
exponential renewals.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsPoissonRandomMeasure

/-- **Long-run intensity of temporal Poisson counts.** Almost surely the natural count
of `(0,t]` per unit time tends to the homogeneous intensity, including intensity zero.
Convergence is along all real nonnegative times, not merely the integer skeleton. -/
theorem ae_tendsto_nat_count_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ≥0 ↦ (⌊(M ω (Ioc 0 t)).toNNReal⌋₊ : ℝ) / t) atTop (𝓝 (r : ℝ)) := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  exact h.hasIndepIncrements_nat_count.ae_tendsto_div_of_hasLaw_poissonMeasure
    h.ae_monotone_nat_count
    (fun _ _ hst ↦ h.hasLaw_nat_count_sub_smul_nnvolume hst)

end TauCeti.Probability.IsPoissonRandomMeasure
