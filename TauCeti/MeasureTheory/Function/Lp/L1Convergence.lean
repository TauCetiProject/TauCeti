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
in `TauCeti.MeasureTheory.Function.Lp.Restriction` and is available through this module.

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
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h
  have hq : (1 : ℝ) ≤ q.toReal ∨ q = ∞ := by
    rcases eq_or_ne q ∞ with rfl | hq
    · exact Or.inr rfl
    · exact Or.inl (by simpa using ENNReal.toReal_mono hq (Fact.out : 1 ≤ q))
  have hC : ν Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / q.toReal) ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_ne_top ν _)
    rcases hq with hq | rfl
    · simpa using inv_le_one_of_one_le₀ hq
    · simp
  have h2 := ENNReal.Tendsto.mul_const h (Or.inr hC)
  rw [zero_mul] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => ?_
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (p := 1) (q := q)
    (Fact.out : 1 ≤ q) (Lp.aestronglyMeasurable (f i - g))
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _)] at h1
  refine (lintegral_congr_ae ?_).trans_le (h1.trans_eq ?_)
  · filter_upwards [Lp.coeFn_sub (f i) g] with x hx
    rw [hx, Pi.sub_apply]
  · rw [eLpNorm_congr_ae (Lp.coeFn_sub (f i) g)]

end TauCeti
