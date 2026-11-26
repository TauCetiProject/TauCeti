/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.PNat.Basic

/-!
# Geometric series indexed by positive integers

A real geometric series over the positive integers sums to `r / (1 - r)` for `|r| < 1`.
-/

public section

/-- The real geometric series over the positive integers sums to `r / (1 - r)`. -/
theorem hasSum_geometric_pnat {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ+ ↦ r ^ (n : ℕ)) (r / (1 - r)) := by
  refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ r ^ n)).2 ?_
  simpa only [pow_succ', div_eq_mul_inv] using (hasSum_geometric_of_abs_lt_one hr).mul_left r
