/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

import TauCeti.MeasureTheory.Measure.Tail
import TauCeti.Probability.Moments.SubGaussian

/-!
# Two-sided sub-Gaussian tail bounds for pre-Brownian increments

For a pre-Brownian process `B` (`ProbabilityTheory.IsPreBrownianReal B P`) and any times
`s, t : ℝ≥0`, the increment `B s - B t` has centered Gaussian law with variance `dist s t`, so it
is `nndist s t`-sub-Gaussian. Combining the upper and lower Chernoff bounds via
`TauCeti.measureReal_le_abs_le_add` bounds both the closed and strict two-sided tails by
`2 * exp (-u ^ 2 / (2 * dist s t))` for `0 ≤ u`. Neither path continuity nor a filtration is
required.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.measureReal_le_abs_sub_le`,
  `ProbabilityTheory.IsPreBrownianReal.measureReal_lt_abs_sub_le`: real-valued two-sided tail
  bounds for `|B s - B t|`.
* `ProbabilityTheory.IsPreBrownianReal.measure_le_abs_sub_le`,
  `ProbabilityTheory.IsPreBrownianReal.measure_lt_abs_sub_le`: `ℝ≥0∞`-valued counterparts.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Real-valued two-sided sub-Gaussian Chernoff bound for the closed tail
`{ω | u ≤ |B s ω - B t ω|}` of a pre-Brownian increment. -/
theorem measureReal_le_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |B s ω - B t ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * dist s t)) := by
  have hsub : HasSubgaussianMGF (B s - B t) (nndist s.1 t.1) P :=
    (hB.hasLaw_sub s t).hasSubgaussianMGF
  calc P.real {ω | u ≤ |B s ω - B t ω|}
      = P.real {ω | u ≤ |(B s - B t) ω|} := rfl
    _ ≤ P.real {ω | u ≤ (B s - B t) ω} + P.real {ω | u ≤ -(B s - B t) ω} :=
        TauCeti.measureReal_le_abs_le_add (f := B s - B t)
    _ ≤ Real.exp (-u ^ 2 / (2 * ↑(nndist s.1 t.1))) +
          Real.exp (-u ^ 2 / (2 * ↑(nndist s.1 t.1))) :=
        add_le_add (hsub.measure_ge_le hu) (hsub.neg.measure_ge_le hu)
    _ = 2 * Real.exp (-u ^ 2 / (2 * dist s t)) := by
        rw [coe_nndist, NNReal.val_eq_coe, NNReal.val_eq_coe, Real.dist_eq, NNReal.dist_eq,
          ← two_mul]

/-- Real-valued two-sided sub-Gaussian Chernoff bound for the strict tail
`{ω | u < |B s ω - B t ω|}` of a pre-Brownian increment. -/
theorem measureReal_lt_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u < |B s ω - B t ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * dist s t)) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (hB.measureReal_le_abs_sub_le s t hu).trans' (measureReal_mono fun _ (hω : u < _) ↦ hω.le)

/-- Two-sided sub-Gaussian Chernoff bound for the closed tail `{ω | u ≤ |B s ω - B t ω|}` of a
pre-Brownian increment. -/
theorem measure_le_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u ≤ |B s ω - B t ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * dist s t))) := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hB.measureReal_le_abs_sub_le s t hu)

/-- Two-sided sub-Gaussian Chernoff bound for the strict tail `{ω | u < |B s ω - B t ω|}` of a
pre-Brownian increment. -/
theorem measure_lt_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u < |B s ω - B t ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * dist s t))) :=
  (hB.measure_le_abs_sub_le s t hu).trans' (measure_mono fun _ (hω : u < _) ↦ hω.le)

end ProbabilityTheory.IsPreBrownianReal
