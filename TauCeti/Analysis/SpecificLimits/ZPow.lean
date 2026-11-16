/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Limits of integer powers

For a real base `b > 1`, the integer powers `b ^ n` tend to `∞` as `n → ∞` and to `0` as
`n → -∞` along the integers. These are the scales `2^j`, `j ∈ ℤ`, of homogeneous dyadic
decompositions.
-/

public section

open Filter Topology

namespace TauCeti

/-- For `b > 1`, `b ^ n → ∞` as `n → ∞` along the integers. -/
theorem tendsto_zpow_atTop_atTop_of_one_lt {b : ℝ} (hb : 1 < b) :
    Tendsto (fun n : ℤ ↦ b ^ n) atTop atTop := by
  simpa only [Function.comp_def, id_eq, Real.rpow_intCast] using
    (tendsto_rpow_atTop_of_base_gt_one b hb).comp
      ((tendsto_intCast_atTop_iff (R := ℝ)).2 tendsto_id)

/-- For `b > 1`, `b ^ n → 0` as `n → -∞` along the integers. -/
theorem tendsto_zpow_atBot_nhds_zero_of_one_lt {b : ℝ} (hb : 1 < b) :
    Tendsto (fun n : ℤ ↦ b ^ n) atBot (𝓝 0) := by
  simpa only [Function.comp_def, id_eq, Real.rpow_intCast] using
    (tendsto_rpow_atBot_of_base_gt_one b hb).comp
      ((tendsto_intCast_atBot_iff (R := ℝ)).2 tendsto_id)

end TauCeti
