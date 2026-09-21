/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

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
    {ν : Measure α} [IsFiniteMeasure ν] [NormedAddCommGroup G] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ∞) {l : Filter ι} {f : ι → Lp G q ν} {g : Lp G q ν} (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun i => ∫⁻ x, ‖f i x - g x‖ₑ ∂ν) l (𝓝 0) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  set C : ℝ≥0∞ := ν Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / q.toReal) with hC
  have hCtop : C ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_ne_top ν _)
    have hq' : (1 : ℝ) ≤ q.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by simp) hq).2 hq1
    have : 1 / q.toReal ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hq'
    simpa using this
  have hmain : Tendsto (fun i => eLpNorm (⇑(f i) - ⇑g) q ν * C) l (𝓝 0) := by
    have h0 : Tendsto (fun i => eLpNorm (⇑(f i) - ⇑g) q ν) l (𝓝 0) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).1 h
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hCtop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmain
    (fun _ => zero_le) fun i => ?_
  have hmeas : AEStronglyMeasurable (⇑(f i) - ⇑g) ν :=
    (Lp.aestronglyMeasurable (f i)).sub (Lp.aestronglyMeasurable g)
  calc ∫⁻ x, ‖f i x - g x‖ₑ ∂ν = eLpNorm (⇑(f i) - ⇑g) 1 ν := by
        rw [eLpNorm_one_eq_lintegral_enorm]; rfl
    _ ≤ eLpNorm (⇑(f i) - ⇑g) q ν * C := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq1 hmeas

end TauCeti
