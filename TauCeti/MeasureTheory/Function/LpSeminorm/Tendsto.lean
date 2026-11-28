/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Convergence to zero of `Lᵖ` seminorms from pointwise smallness

If a family `f i` is eventually bounded almost everywhere by `δ ‖b‖ₑ` for every `δ > 0`, where `b`
has finite `Lᵖ` seminorm, then `eLpNorm (f i) p μ → 0`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_le_mul`). Taking `b = 1` on a finite measure space,
a family that eventually becomes uniformly small almost everywhere tends to `0` in every `Lᵖ`
(`TauCeti.tendsto_eLpNorm_zero_of_eventually_ae_le`). This is how uniform convergence on a set of
finite measure, or uniform convergence of a coefficient multiplying a fixed `Lᵖ` function, is
turned into convergence in `Lᵖ`. No lower bound on `p` is needed.

The case `p = ∞` needs no finiteness of the measure. A family of fields `M ν`, depending on a
parameter `ν` in a topological space `X`, which is jointly continuous at every point of `{ν₀} × K`
for a compact set `K` and, for `ν` near `ν₀`, agrees with `M ν₀` off `K`, converges uniformly on
`K` as `ν → ν₀`
(`IsCompact.tendstoUniformlyOn_of_continuousAt`), so `M ν → M ν₀` in `L^∞`
(`TauCeti.tendsto_eLpNorm_top_sub_of_continuousAt_of_eq`). This is how a family of coefficient
fields that is only modified on a compact part of a noncompact domain is seen to depend continuously
on its parameter in `L^∞`.
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

/-- **`L^∞` continuity of a family modified on a compact set.** Let `M ν` be fields on a
measurable set `S`, depending on a parameter `ν` in a topological space `X`, which are jointly
continuous in `(ν, z)` at every point of `{ν₀} × K` for a compact set `K`. Suppose that for `ν`
near `ν₀` the field `M ν` is almost everywhere strongly measurable on `S` and agrees with `M ν₀` at
the points of `S` outside `K`. Then `M ν → M ν₀` in `L^∞(S)` as `ν → ν₀`. -/
theorem tendsto_eLpNorm_top_sub_of_continuousAt_of_eq {X α E : Type*} [TopologicalSpace X]
    [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    {M : X → α → E} {S K : Set α} (hS : MeasurableSet S) (hK : IsCompact K)
    {ν₀ : X} (hmeas : ∀ᶠ ν in 𝓝 ν₀, AEStronglyMeasurable (M ν) (μ.restrict S))
    (hM : ∀ z ∈ K, ContinuousAt (Function.uncurry M) (ν₀, z))
    (heq : ∀ᶠ ν in 𝓝 ν₀, ∀ z ∈ S, z ∉ K → M ν z = M ν₀ z) :
    Tendsto (fun ν => eLpNorm (M ν - M ν₀) ∞ (μ.restrict S)) (𝓝 ν₀) (𝓝 0) := by
  refine tendsto_eLpNorm_zero_of_eventually_le_mul (b := fun _ => (1 : ℝ))
    (memLp_top_const 1).eLpNorm_ne_top (hmeas.mono fun ν hν => hν.sub hmeas.self_of_nhds)
    fun δ hδ => ?_
  -- On the compact set `K` the family converges uniformly.
  filter_upwards [hK.tendstoUniformlyOn_of_continuousAt hM _
    (Metric.dist_mem_uniformity (NNReal.coe_pos.2 hδ)), heq] with ν hν hνK
  filter_upwards [ae_restrict_mem hS] with z hz
  rw [eNorm_one, mul_one, Pi.sub_apply, ← eDist_eq_eNorm_sub]
  by_cases hzK : z ∈ K
  · exact (edist_lt_coe.2 (by simpa [nndist_comm] using hν z hzK)).le
  · rw [hνK z hz hzK, edist_self]
    exact zero_le

end TauCeti
