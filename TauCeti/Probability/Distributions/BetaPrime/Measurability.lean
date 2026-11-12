/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaPrime.Basic
import all TauCeti.Probability.Distributions.BetaPrime.Basic
import TauCeti.Probability.Distributions.Beta.Measurability

/-!
# Parameter measurability of beta-prime laws

This file proves joint measurability of the beta-prime density and of the measure-valued family
in its two shape parameters.  Invalid parameters are included, where both the density and the law
are zero.

## Main results

* `TauCeti.Probability.measurable_uncurry_betaPrimePDF` — joint measurability of the density;
* `TauCeti.Probability.measurable_betaPrimeMeasure` — joint parameter measurability of the law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The beta-prime density is jointly measurable in both shape parameters and the sample point. -/
@[fun_prop]
theorem measurable_uncurry_betaPrimePDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ betaPrimePDF q.1.1 q.1.2 q.2 := by
  unfold betaPrimePDF betaPrimePDFReal
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  have hzero : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ) := measurable_const
  exact (measurableSet_lt hzero measurable_fst.fst).inter
    ((measurableSet_lt hzero measurable_fst.snd).inter
      (measurableSet_lt hzero measurable_snd))

/-- The beta-prime family is jointly measurable in its two shape parameters. -/
@[fun_prop]
theorem measurable_betaPrimeMeasure :
    Measurable fun p : ℝ × ℝ ↦ betaPrimeMeasure p.1 p.2 := by
  simpa only [betaPrimeMeasure_eq_withDensity] using
    measurable_withDensity (μ := volume) measurable_uncurry_betaPrimePDF

end TauCeti.Probability
