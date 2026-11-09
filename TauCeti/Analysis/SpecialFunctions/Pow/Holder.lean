/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Hölder continuity of real powers

For `0 ≤ p ≤ 1` the power `t ↦ t ^ p` is `p`-Hölder on `[0, ∞)` with constant one:
`|a ^ p - b ^ p| ≤ |a - b| ^ p` for `a, b ≥ 0`. This is the subadditivity
`(a + b) ^ p ≤ a ^ p + b ^ p` of Mathlib's `Real.rpow_add_le_add_rpow`, applied to `b` and
`a - b`. It is the estimate showing that cone-point functions such as `‖z‖ ^ p` are `p`-Hölder.
-/

public section

namespace Real

/-- On `[0, ∞)` the power `t ↦ t ^ p` is `p`-Hölder with constant one, for `0 ≤ p ≤ 1`. -/
theorem abs_rpow_sub_rpow_le {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) : |a ^ p - b ^ p| ≤ |a - b| ^ p := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have h := rpow_add_le_add_rpow (sub_nonneg.mpr hab) hb hp hp1
  rw [sub_add_cancel] at h
  rw [abs_of_nonneg (sub_nonneg.mpr (rpow_le_rpow hb hab hp)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  linarith

end Real
