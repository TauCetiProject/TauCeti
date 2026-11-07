/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Closed annuli in normed groups

The closed annulus `{z | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b}` about `c` is compact in a proper space
(`Metric.isCompact_annulus`), and when its inner radius is positive it does not contain its centre
(`Metric.ne_of_mem_annulus`). A point of a normed ring within distance `1` of `1` is not `0`
(`ne_zero_of_norm_sub_one_lt`).
-/

public section

open Metric Set

/-- A point within distance `1` of `1` is not `0`. -/
theorem ne_zero_of_norm_sub_one_lt {R : Type*} [SeminormedRing R] [NormOneClass R] {z : R}
    (hz : ‖z - 1‖ < 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

namespace Metric

/-- A point of a closed annulus with positive inner radius is not its centre. -/
theorem ne_of_mem_annulus {E : Type*} [SeminormedAddCommGroup E] {c z : E} {r ρ : ℝ}
    (hr : 0 < r) (hz : z ∈ {z : E | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ ρ}) : z ≠ c := by
  rintro rfl
  have := hz.1
  simp only [sub_self, norm_zero] at this
  linarith

/-- A closed annulus is compact in a proper space. -/
theorem isCompact_annulus {E : Type*} [SeminormedAddCommGroup E] [ProperSpace E] (c : E)
    (a b : ℝ) : IsCompact {z : E | a ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ b} :=
  (isCompact_closedBall c b).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const))
    fun z hz ↦ by rw [mem_closedBall, dist_eq_norm]; exact hz.2

end Metric
