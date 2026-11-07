/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Probability.Distributions.MarchenkoPastur.Basic
import TauCeti.Probability.Distributions.MarchenkoPastur.Moments
import TauCeti.Probability.Moments.MethodOfMoments.CompactSupport

/-!
# Weak continuity of Marchenko–Pastur laws

The Marchenko–Pastur laws `marchenkoPastur y` depend weakly continuously on the aspect ratio
`y : ℝ≥0`, including across the critical ratio `y = 1` (where the atom at `0` emerges) and at the
zero-ratio boundary `y = 0` (where `marchenkoPastur 0 = δ₁`).

Because every Marchenko–Pastur law is compactly supported and its `k`-th moment is a polynomial in
`y` (`integral_pow_marchenkoPastur`), weak continuity follows immediately from the method of
moments (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow`).

## Main declarations

* `TauCeti.Probability.continuous_integral_pow_marchenkoPastur`: each moment `y ↦ ∫ x ^ k dMP_y` is
  continuous on `ℝ≥0`.
* `TauCeti.Probability.continuous_marchenkoPastur`: `y ↦ (marchenkoPastur y).toProbabilityMeasure`
  is continuous on `ℝ≥0`.
* `TauCeti.Probability.tendsto_marchenkoPastur_nhds_zero_dirac`: `MP_y → δ₁` weakly as `y → 0`.
* `Continuous.marchenkoPastur`: `fun_prop` rule for continuous parameterizations.

## References

* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- For every `k : ℕ`, the `k`-th moment `y ↦ ∫ x ^ k d(marchenkoPastur y)` is continuous on
`ℝ≥0`. -/
@[fun_prop]
theorem continuous_integral_pow_marchenkoPastur (k : ℕ) :
    Continuous fun y : ℝ≥0 ↦ ∫ x, x ^ k ∂marchenkoPastur y := by
  simp_rw [integral_pow_marchenkoPastur]
  fun_prop

/-- Marchenko–Pastur laws depend weakly continuously on the aspect ratio `y : ℝ≥0`, including
across `y = 1` and at the Dirac boundary `y = 0`. -/
theorem continuous_marchenkoPastur :
    Continuous fun y : ℝ≥0 ↦ (marchenkoPastur y).toProbabilityMeasure := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  refine ProbabilityMeasure.tendsto_of_tendsto_integral_pow
    (K := Icc 0 ((1 + √(y₀ : ℝ)) ^ 2)) isCompact_Icc ?_
    (fun n ↦ Eventually.of_forall fun y ↦ ?_) fun n ↦ ?_
  · rw [Measure.coe_toProbabilityMeasure]
    exact ae_iff.1 (ae_mem_Icc_zero_marchenkoPastur y₀)
  · simpa using integrable_pow_marchenkoPastur y n
  · simpa using (continuous_integral_pow_marchenkoPastur n).continuousAt.tendsto

/-- As the aspect ratio tends to `0`, `marchenkoPastur y` converges weakly to the point mass at
`1`. -/
theorem tendsto_marchenkoPastur_nhds_zero_dirac :
    Tendsto (fun y : ℝ≥0 ↦ (marchenkoPastur y).toProbabilityMeasure) (𝓝 0)
      (𝓝 (Measure.dirac 1).toProbabilityMeasure) := by
  simpa [marchenkoPastur_zero] using continuous_marchenkoPastur.tendsto 0

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- A continuous aspect-ratio parameter gives a weakly continuous Marchenko–Pastur law, including
at the zero-ratio Dirac boundary `δ₁`. -/
@[fun_prop]
theorem marchenkoPastur {y : T → ℝ≥0} (hy : Continuous y) :
    Continuous fun t ↦ (TauCeti.Probability.marchenkoPastur (y t)).toProbabilityMeasure :=
  TauCeti.Probability.continuous_marchenkoPastur.comp hy

end Continuous
