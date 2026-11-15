/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Convergence to zero of `Lᵖ` seminorms from pointwise smallness

If a family `f i` is eventually bounded almost everywhere by `δ ‖b‖ₑ` for every `δ > 0`, where `b`
has finite `Lᵖ` seminorm, then `eLpNorm (f i) p μ → 0`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_le_mul`). Taking `b = 1` on a finite measure space,
a family that eventually becomes uniformly small almost everywhere tends to `0` in every `Lᵖ`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_ae_le`). This is how uniform convergence on a set of
finite measure, or uniform convergence of a coefficient multiplying a fixed `Lᵖ` function, is
turned into convergence in `Lᵖ`. No lower bound on `p` is needed.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α ι ε ε' : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε]
  [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] {p : ℝ≥0∞} {l : Filter ι}
  {f : ι → α → ε}

/-- If `f i` is eventually bounded by `δ ‖b‖ₑ` for every `δ > 0`, and `b` has finite `Lᵖ` norm, then
the `Lᵖ` norm of `f i` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_eventually_le_mul {b : α → ε'} (hb : eLpNorm b p μ ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ₑ ≤ δ * ‖b x‖ₑ) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hb hε.ne'
  filter_upwards [hf, h δ hδ] with i hfi hi
  exact (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfi hi p).trans hδε.le

/-- On a finite measure space, if for every `δ > 0` eventually `‖f i‖ₑ ≤ δ` almost everywhere, then
the `Lᵖ` norm of `f i` tends to `0`. -/
theorem tendsto_eLpNorm_zero_of_eventually_ae_le [IsFiniteMeasure μ]
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (h : ∀ δ : ℝ≥0, 0 < δ → ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ₑ ≤ δ) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
    (memLp_const 1).eLpNorm_ne_top hf fun δ hδ => ?_
  filter_upwards [h δ hδ] with i hi
  filter_upwards [hi] with x hx
  simpa using hx

end TauCeti
