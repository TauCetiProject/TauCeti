/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Closedness of sets of points around which a set is sparse

In a pseudometric space, the points `x` around which a set `A` fills at most a prescribed amount
`K r` of every open ball `ball x r` of radius `r < ρ` form a closed set
(`TauCeti.isClosed_setOf_forall_measure_inter_ball_le`): the measure of `A ∩ ball x r` is the
supremum over smaller radii of measures controlled at nearby points
(`MeasureTheory.Measure.measure_ball_le_of_forall_lt`).
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The points around which a set fills at most a prescribed amount `K r` of every open ball of
radius `r < ρ` form a closed set. -/
theorem isClosed_setOf_forall_measure_inter_ball_le (μ : Measure X) (A : Set X) (ρ : ℝ)
    (K : ℝ → ℝ≥0∞) : IsClosed {x | ∀ r ∈ Ioo 0 ρ, μ (A ∩ ball x r) ≤ K r} := by
  refine closure_subset_iff_isClosed.1 fun x hx r hr => ?_
  have hrestr (z : X) (ρ' : ℝ) : μ (A ∩ ball z ρ') = μ.restrict A (ball z ρ') := by
    rw [Measure.restrict_apply measurableSet_ball, inter_comm]
  rw [hrestr]
  refine Measure.measure_ball_le_of_forall_lt _ fun r' hr' => ?_
  obtain ⟨x', hx', hxx'⟩ := Metric.mem_closure_iff.1 hx (r - r') (sub_pos.2 hr')
  rw [← hrestr]
  calc μ (A ∩ ball x r') ≤ μ (A ∩ ball x' r) :=
        measure_mono (inter_subset_inter_right _ (ball_subset_ball' (by linarith)))
    _ ≤ K r := hx' r hr

end TauCeti
