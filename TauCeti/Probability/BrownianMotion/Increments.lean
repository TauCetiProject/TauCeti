/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic

import TauCeti.Probability.Moments.SubGaussian

/-!
# Two-sided sub-Gaussian tail bounds for pre-Brownian increments

For a pre-Brownian process `B` (`ProbabilityTheory.IsPreBrownianReal B P`) and any times
`s, t : ℝ≥0`, the increment `B s - B t` has centered Gaussian law with variance `dist s t`, so it
is `nndist s t`-sub-Gaussian via `ProbabilityTheory.HasLaw.hasSubgaussianMGF`. Specializing the
general two-sided Chernoff tail bounds (`ProbabilityTheory.HasSubgaussianMGF.measureReal_le_abs_le`
and its strict-tail and `ℝ≥0∞` counterparts) bounds both the closed and strict two-sided tails by
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

private lemma coe_nndist_val (s t : ℝ≥0) : ((nndist s.1 t.1 : ℝ≥0) : ℝ) = dist s t := by
  rw [coe_nndist, NNReal.val_eq_coe, NNReal.val_eq_coe, Real.dist_eq, NNReal.dist_eq]

/-- Real-valued two-sided sub-Gaussian Chernoff bound for the closed tail
`{ω | u ≤ |B s ω - B t ω|}` of a pre-Brownian increment. -/
theorem measureReal_le_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ |B s ω - B t ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * dist s t)) :=
  ((hB.hasLaw_sub s t).hasSubgaussianMGF.measureReal_le_abs_le hu).trans_eq
    (by rw [coe_nndist_val])

/-- Real-valued two-sided sub-Gaussian Chernoff bound for the strict tail
`{ω | u < |B s ω - B t ω|}` of a pre-Brownian increment. -/
theorem measureReal_lt_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u < |B s ω - B t ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * dist s t)) :=
  ((hB.hasLaw_sub s t).hasSubgaussianMGF.measureReal_lt_abs_le hu).trans_eq
    (by rw [coe_nndist_val])

/-- Two-sided sub-Gaussian Chernoff bound for the closed tail `{ω | u ≤ |B s ω - B t ω|}` of a
pre-Brownian increment. -/
theorem measure_le_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u ≤ |B s ω - B t ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * dist s t))) :=
  ((hB.hasLaw_sub s t).hasSubgaussianMGF.measure_le_abs_le hu).trans_eq
    (by rw [coe_nndist_val])

/-- Two-sided sub-Gaussian Chernoff bound for the strict tail `{ω | u < |B s ω - B t ω|}` of a
pre-Brownian increment. -/
theorem measure_lt_abs_sub_le (hB : IsPreBrownianReal B P) (s t : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    P {ω | u < |B s ω - B t ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * dist s t))) :=
  ((hB.hasLaw_sub s t).hasSubgaussianMGF.measure_lt_abs_le hu).trans_eq
    (by rw [coe_nndist_val])

end ProbabilityTheory.IsPreBrownianReal
