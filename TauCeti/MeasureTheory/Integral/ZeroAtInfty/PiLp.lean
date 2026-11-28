/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Bochner.PiLp
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Weighted `PiLp` integrals of functions vanishing at infinity

Specializing `TauCeti.norm_toLp_integral_weighted_le` to a map `f : C₀(Ω, PiLp p β)` and an
almost everywhere nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0` yields
`‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`
(`ZeroAtInftyContinuousMap.norm_toLp_integral_weighted_le`).
-/

public section

open MeasureTheory
open scoped ENNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-- Weighted integral norm bound in `PiLp`: for `f : C₀(Ω, PiLp p β)` with `1 ≤ p ≤ ∞` and
seminormed additive commutative group fibers `β i`, and an almost everywhere nonnegative integrable
weight `w` of total mass `∫ w ∂μ = α > 0`, `‖toLp p (i ↦ α⁻¹ * ∫ ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖`. -/
theorem norm_toLp_integral_weighted_le {Ω ι : Type*} [Fintype ι] [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] (f : C₀(Ω, PiLp p β)) {w : Ω → ℝ}
    {α : ℝ} (hα : 0 < α) (hw_int : Integrable w μ) (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hw_sum : ∫ t, w t ∂μ = α) :
    ‖WithLp.toLp p (fun i ↦ α⁻¹ * ∫ t, ‖f t i‖ * w t ∂μ)‖ ≤ ‖f‖ :=
  TauCeti.norm_toLp_integral_weighted_le f
    (fun i ↦ ((PiLp.continuous_apply p β i).comp f.continuous).norm.aemeasurable)
    (ae_of_all _ fun t ↦ norm_coe_le_norm f t) hα hw_int hw_nonneg hw_sum

end ZeroAtInftyContinuousMap
