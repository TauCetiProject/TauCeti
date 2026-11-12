/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Positive scaling of log-normal laws

Multiplying a log-normal variable by a positive constant `b` adds `log b` to its
log-mean and preserves its log-variance. Thus all log-means can be obtained by
scaling the law with log-mean zero. The measure identity and its random-variable
form include the zero-variance Dirac boundary.

In logarithmic coordinates, positive scaling by `b` corresponds to translation
by `log b`.

## References

* Mathlib, `ProbabilityTheory.gaussianReal_map_add_const` (Gaussian translation).
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*,
  vol. 1, 2nd ed., Wiley (1994), ch. 14.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped NNReal

namespace TauCeti.Probability

/-- Positive scaling adds the logarithm of the multiplier to the log-mean,
including when the log-variance is zero. -/
@[simp]
theorem logNormalMeasure_map_const_mul {b : ℝ} (hb : 0 < b) (m : ℝ) (v : ℝ≥0) :
    (logNormalMeasure m v).map (fun x ↦ b * x) =
      logNormalMeasure (m + Real.log b) v := by
  rw [logNormalMeasure_map_exp, logNormalMeasure_map_exp,
    ← gaussianReal_map_add_const (Real.log b),
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [Real.exp_add, Real.exp_log hb, mul_comm]

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- Multiplying a log-normal random variable by a positive constant shifts its log-mean
by the logarithm of that constant and preserves its log-variance. -/
theorem HasLaw.const_mul_logNormalMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (logNormalMeasure m v) P) {b : ℝ} (hb : 0 < b) :
    HasLaw (fun ω ↦ b * X ω) (logNormalMeasure (m + Real.log b) v) P := by
  rw [← logNormalMeasure_map_const_mul hb]
  exact (hasLaw_map (measurable_const_mul b).aemeasurable).fun_comp hX

end ProbabilityTheory
