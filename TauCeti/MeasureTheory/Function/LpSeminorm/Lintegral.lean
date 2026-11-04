/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# The `Lᵖ` integral is bounded by the `p`-th power of the `Lᵖ` seminorm

For a finite exponent `p ≠ 0`, Mathlib's `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral` identifies
`eLpNorm f p μ ^ p` with `∫⁻ ‖f‖ₑ ^ p ∂μ` for an almost everywhere strongly measurable `f`. Without
measurability the seminorm is `∞` by convention, so the inequality
`∫⁻ ‖f‖ₑ ^ p ∂μ ≤ eLpNorm f p μ ^ p` holds for every `f`
(`TauCeti.lintegral_rpow_enorm_le_rpow_eLpNorm`). This is the form in which a bound on the `Lᵖ`
seminorm is used to bound an integral, with no measurability side condition.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal NNReal

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

/-- For `p ≠ 0`, the integral `∫⁻ ‖f‖ₑ ^ p ∂μ` is at most `eLpNorm f p μ ^ p`, whether or not `f` is
almost everywhere strongly measurable. -/
theorem lintegral_rpow_enorm_le_rpow_eLpNorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → ε) :
    ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ ≤ eLpNorm f p μ ^ (p : ℝ) := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_nnreal_pow_eq_lintegral hp hf).ge
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.top_rpow_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp))]
    exact le_top

end TauCeti
