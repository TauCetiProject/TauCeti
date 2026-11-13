/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Small `Lᵖ` seminorms on small closed balls

An `Lᵖ` function, `1 ≤ p < ∞`, has arbitrarily small `Lᵖ` seminorm on small enough closed balls
about a point of measure zero (`TauCeti.exists_eLpNorm_indicator_closedBall_le`), for a measure
that is finite on compact subsets of a proper metric space. This is the absolute continuity of
the `Lᵖ` seminorm combined with the shrinking of the measure of small balls to that of their
centre. It chooses the small discs on which an `Lᵖ` coefficient of a linear elliptic equation is
small, as in the similarity principle with `Lᵖ` coefficients.
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

variable {X F : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [ProperSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F]

/-- An `Lᵖ` function, `1 ≤ p < ∞`, has arbitrarily small `Lᵖ` seminorm on small enough closed balls
about a point of measure zero. -/
theorem exists_eLpNorm_indicator_closedBall_le {G : X → F} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (hG : MemLp G p μ) {x₀ : X} (h₀ : μ {x₀} = 0) {R : ℝ} {ε : ℝ≥0∞} (hR : 0 < R)
    (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r ≤ R ∧ eLpNorm ((closedBall x₀ r).indicator G) p μ ≤ ε := by
  obtain ⟨δ, hδ, hδG⟩ := hG.eLpNorm_indicator_le hp1 hp hε
  have ht := tendsto_measure_cthickening_of_isCompact (μ := μ) (isCompact_singleton (x := x₀))
  rw [h₀] at ht
  obtain ⟨η, hη, hηδ⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (gt_mem_nhds hδ))
  have hr : 0 < min (η / 2) R := lt_min (by positivity) hR
  refine ⟨min (η / 2) R, hr, min_le_right _ _,
    hδG _ measurableSet_closedBall.nullMeasurableSet ?_⟩
  refine (measure_mono (closedBall_subset_cthickening_singleton x₀ _)).trans (hηδ ?_).le
  rw [Real.dist_eq, sub_zero, abs_of_pos hr]
  exact (min_le_left _ _).trans_lt (half_lt_self hη)

end TauCeti
