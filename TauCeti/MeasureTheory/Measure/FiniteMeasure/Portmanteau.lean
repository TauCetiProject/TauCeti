/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Continuity sets for finite measures

Weak convergence of finite measures implies convergence of their masses on sets with
null boundary. This extends the probability-measure portmanteau API to finite measures,
including the zero limit, and is useful when localizing locally finite measures.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory.FiniteMeasure

variable {X ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [HasOuterApproxClosed X] {l : Filter ι}
  {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}

/-- Weak convergence of finite measures gives convergence on every continuity set of the
limit measure. No measurability assumption on the set is needed. -/
theorem tendsto_measure_of_null_frontier_of_tendsto
    (h : Tendsto μs l (𝓝 μ)) {s : Set X} (hs : (μ : Measure X) (frontier s) = 0) :
    Tendsto (fun i ↦ (μs i : Measure X) s) l (𝓝 ((μ : Measure X) s)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simpa only [Set.eq_empty_of_isEmpty s, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  by_cases hμ : μ = 0
  · subst μ
    simp only [toMeasure_zero, FunLike.coe_zero, Pi.zero_apply]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [Function.comp_def, ennreal_mass, zero_mass, ENNReal.coe_zero] using
        (ENNReal.continuous_coe.tendsto _).comp h.mass)
      (fun _ ↦ bot_le) (fun _ ↦ measure_mono (subset_univ s))
  · have hn := tendsto_normalize_of_tendsto h hμ
    have hboundary : (μ.normalize : Measure X) (frontier s) = 0 := by
      simp [toMeasure_normalize_eq_of_ne_zero μ hμ, hs]
    have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn
      (by simpa only [ProbabilityMeasure.null_iff_toMeasure_null] using hboundary)
    have hprod := h.mass.mul hp
    simp_rw [← self_eq_mass_mul_normalize] at hprod
    simpa only [Function.comp_def, ennreal_coeFn_eq_coeFn_toMeasure] using
      (ENNReal.continuous_coe.tendsto _).comp hprod

end MeasureTheory.FiniteMeasure
