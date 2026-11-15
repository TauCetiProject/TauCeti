/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Weibull.Basic
import TauCeti.Probability.Distributions.GeneralizedGamma.Relations

/-!
# Positive scaling of Weibull laws

Multiplying a Weibull variable by a positive constant preserves its shape and multiplies
its scale by that constant. This allows the unit-scale law to represent every positive
scale and gives the corresponding transport rule for random variables.

The measure identity specializes `generalizedGammaMeasure_map_const_mul` through
`generalizedGammaMeasure_one_shape_eq_weibullMeasure`. It also holds for nonpositive
shape or scale, where the Weibull law is zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Positive scaling multiplies the Weibull scale and preserves its shape, including
the zero laws at invalid parameters. -/
@[simp]
theorem weibullMeasure_map_const_mul {b : ℝ} (hb : 0 < b) (k s : ℝ) :
    (weibullMeasure k s).map (fun x ↦ b * x) = weibullMeasure k (b * s) := by
  by_cases hk : 0 < k
  · rw [← generalizedGammaMeasure_one_shape_eq_weibullMeasure hk,
      generalizedGammaMeasure_map_const_mul hb,
      generalizedGammaMeasure_one_shape_eq_weibullMeasure hk]
  · simp [weibullMeasure_of_not_pos (by tauto : ¬ (0 < k ∧ 0 < s)),
      weibullMeasure_of_not_pos (by tauto : ¬ (0 < k ∧ 0 < b * s))]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Multiplying a Weibull random variable by a positive constant multiplies its scale. -/
theorem HasLaw.const_mul_weibullMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {k s : ℝ} (hX : HasLaw X (weibullMeasure k s) P)
    {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ b * X ω) (weibullMeasure k (b * s)) P := by
  rw [← weibullMeasure_map_const_mul hb]
  exact (hasLaw_map (measurable_const_mul b).aemeasurable).fun_comp hX

end ProbabilityTheory
