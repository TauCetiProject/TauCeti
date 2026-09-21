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

## Main declarations

* `TauCeti.tendsto_lintegral_enorm_sub_of_tendsto_Lp`: `Lᵖ` convergence gives
  `∫⁻ ‖f i - g‖ₑ → 0`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal Topology

/-- **On a finite measure space, `Lᵖ` convergence implies `L¹` convergence.** -/
theorem tendsto_lintegral_enorm_sub_of_tendsto_Lp {α G ι : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {l : Filter ι} {f : ι → Lp G q ν} {g : Lp G q ν}
    (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun i => ∫⁻ x, ‖f i x - g x‖ₑ ∂ν) l (𝓝 0) := by
  have hL1 : Tendsto
      (fun i => Measure.LpToL1CLM (𝕜 := ℝ) ν q (f i)) l
      (𝓝 (Measure.LpToL1CLM (𝕜 := ℝ) ν q g)) :=
    ((Measure.LpToL1CLM (𝕜 := ℝ) ν q).continuous.tendsto g).comp h
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hL1
  refine hL1.congr fun i => ?_
  rw [eLpNorm_one_eq_lintegral_enorm]
  apply lintegral_congr_ae
  filter_upwards [Measure.LpToL1CLM_coeFn (𝕜 := ℝ) ν q (f i),
    Measure.LpToL1CLM_coeFn (𝕜 := ℝ) ν q g] with x hfi hg
  rw [Pi.sub_apply, hfi, hg]

end TauCeti
