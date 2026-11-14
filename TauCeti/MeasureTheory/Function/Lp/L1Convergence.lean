/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# `Lᵖ` convergence implies `L¹` convergence on a finite measure space

On a finite measure space the `Lᵖ` seminorm dominates the `L¹` seminorm up to the factor
`μ(univ)^(1 - 1/p)`, so a sequence converging in `Lᵖ` converges in `L¹`.  Stated with the `L¹`
distance written as a lower Lebesgue integral, which is the form consumed by arguments that pass
an integral identity to a limit.

The finite-set representative version,
`TauCeti.tendsto_setLIntegral_enorm_sub_of_tendsto_Lp`, lives beside the restriction operator
in `TauCeti.MeasureTheory.Function.Lp.Restriction` and is available through this module; the
statement here is its case of the whole space.

## Main declarations

* `TauCeti.tendsto_lintegral_enorm_sub_of_tendsto_Lp`: `Lᵖ` convergence gives
  `∫⁻ ‖f i - g‖ₑ → 0`.
-/

public section

namespace TauCeti

open Filter _root_.MeasureTheory
open scoped ENNReal Topology

/-- **On a finite measure space, `Lᵖ` convergence implies `L¹` convergence.** -/
theorem tendsto_lintegral_enorm_sub_of_tendsto_Lp {α G ι : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] [NormedAddCommGroup G]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {l : Filter ι} {f : ι → Lp G q ν} {g : Lp G q ν}
    (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun i => ∫⁻ x, ‖f i x - g x‖ₑ ∂ν) l (𝓝 0) := by
  simpa using tendsto_setLIntegral_enorm_sub_of_tendsto_Lp (measure_lt_top ν Set.univ) h
    (fun _ => .rfl) .rfl

end TauCeti
