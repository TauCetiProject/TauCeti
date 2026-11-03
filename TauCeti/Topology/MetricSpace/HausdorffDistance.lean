/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Cutoffs built from the distance to a set

For a set `s` in a pseudometric space and a scale `t > 0`, the cutoff
`x ↦ min 1 (t⁻¹ * infDist x s)` vanishes on `s`, equals `1` at points at distance at least `t`
from `s`, and is `t⁻¹`-Lipschitz. It is the standard Lipschitz approximation of the indicator of
the complement of `s`, increasing to it as `t → 0`.
-/

public section

open Metric

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- The cutoff `min 1 (d / t)`, built from the distance `d` to a set, is `t⁻¹`-Lipschitz. -/
theorem lipschitzWith_min_one_inv_mul_infDist (s : Set X) {t : ℝ} (ht : 0 < t) :
    LipschitzWith (Real.toNNReal t⁻¹) fun x => min 1 (t⁻¹ * infDist x s) := by
  have h1 : LipschitzWith (Real.toNNReal t⁻¹) fun x => t⁻¹ * infDist x s :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 ht),
        Real.coe_toNNReal _ (inv_pos.2 ht).le]
      exact mul_le_mul_of_nonneg_left ((lipschitz_infDist_pt s).dist_le_mul x y |>.trans
        (by simp)) (inv_pos.2 ht).le
  exact h1.const_min 1

/-- The cutoff `min 1 (d / t)` equals `1` where the distance `d` to the set is at least `t`. -/
theorem min_one_inv_mul_infDist_eq_one {s : Set X} {t : ℝ} (ht : 0 < t) {x : X}
    (hx : t ≤ infDist x s) : min 1 (t⁻¹ * infDist x s) = 1 :=
  min_eq_left ((le_inv_mul_iff₀ ht).2 (by simpa using hx))

/-- The cutoff `min 1 (d / t)` vanishes on the set itself. -/
@[simp]
theorem min_one_inv_mul_infDist_eq_zero {s : Set X} (t : ℝ) {x : X} (hx : x ∈ s) :
    min 1 (t⁻¹ * infDist x s) = 0 := by
  rw [infDist_zero_of_mem hx, mul_zero, min_eq_right zero_le_one]

end TauCeti
