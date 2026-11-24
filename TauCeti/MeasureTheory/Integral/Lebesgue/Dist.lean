/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Markov's inequality for a monotone function of the distance

For a measure `μ` on a pseudometric space, a point `θ`, a real `s` and a monotone
`ℓ : ℝ≥0∞ → ℝ≥0∞`, `ℓ (ofReal s) · μ {y | s ≤ dist y θ} ≤ ∫⁻ y, ℓ (edist y θ) ∂μ`. No
measurability of `ℓ` is needed: the set is closed and the lower integral is monotone.

## Main result

* `TauCeti.mul_measure_le_lintegral_edist`

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer (2009), (2.5), p. 79.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- **Markov's inequality for a monotone loss of the distance.** For every measure `μ`, point
`θ`, real `s` and monotone `ℓ`, `ℓ s · μ {y | s ≤ dist y θ} ≤ ∫⁻ y, ℓ (edist y θ) ∂μ`. The loss
need not be measurable. -/
theorem mul_measure_le_lintegral_edist {μ : Measure Y} (θ : Y) (s : ℝ) {ℓ : ℝ≥0∞ → ℝ≥0∞}
    (hℓ : Monotone ℓ) :
    ℓ (ENNReal.ofReal s) * μ {y | s ≤ dist y θ} ≤ ∫⁻ y, ℓ (edist y θ) ∂μ := by
  have hm : MeasurableSet {y | s ≤ dist y θ} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  refine (mul_measure_le_setLIntegral₀ hm.nullMeasurableSet fun y hy ↦ ?_).trans
    (setLIntegral_le_lintegral _ _)
  rw [edist_dist]
  exact hℓ (ENNReal.ofReal_le_ofReal hy)

end TauCeti
