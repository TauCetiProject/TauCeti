/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Probability.Distributions.Gamma.Quantile

/-!
# Quantiles of exponential laws

This file computes the lower quantile of the exponential probability measure with positive rate
`r`. At an interior probability level `u`, it is `-log (1 - u) / r`. Its one-sided endpoint
limits are `0` and positive infinity in `EReal`.

The formula and limits are inherited from the Gamma law with shape one, reflecting Mathlib's
definition of `expMeasure r` as `gammaMeasure 1 r`.

## Main results

* `TauCeti.Probability.quantile_expMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.tendsto_quantile_expMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_expMeasure_nhdsLT_one` give its endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {r u : ℝ}

/-- The lower quantile of an exponential law with positive rate `r` is
`-log (1 - u) / r` at every interior probability level. -/
@[simp]
theorem quantile_expMeasure (hr : 0 < r) (hu : u ∈ Ioo 0 1) :
    (expMeasure r).quantile u = -Real.log (1 - u) / r := by
  rw [expMeasure, quantile_gammaMeasure one_pos hr hu, inverseRegularizedGamma_one hu]

/-- Exponential quantiles tend to the lower support endpoint `0` as the probability level tends
to zero from above. -/
theorem tendsto_quantile_expMeasure_nhdsGT_zero (hr : 0 < r) :
    Tendsto (fun u ↦ ((expMeasure r).quantile u : EReal)) (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  rw [expMeasure]
  exact EReal.tendsto_coe.2
    ((tendsto_quantile_gammaMeasure_nhdsGT_zero one_pos hr).mono_right inf_le_left)

/-- Exponential quantiles tend to positive infinity as the probability level tends to one from
below. -/
theorem tendsto_quantile_expMeasure_nhdsLT_one (hr : 0 < r) :
    Tendsto (fun u ↦ ((expMeasure r).quantile u : EReal)) (nhdsWithin 1 (Iio 1))
      (nhds ⊤) := by
  rw [expMeasure, EReal.tendsto_coe_nhds_top_iff]
  exact tendsto_quantile_gammaMeasure_nhdsLT_one one_pos hr

end TauCeti.Probability
