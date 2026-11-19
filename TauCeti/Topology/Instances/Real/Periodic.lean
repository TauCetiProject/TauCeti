/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real

/-!
# Bounds of continuous periodic real functions

A continuous periodic function `f : ℝ → ℝ` with nonzero period is bounded in absolute value.

## Main results

* `Function.Periodic.exists_forall_abs_le`: a continuous periodic function `f : ℝ → ℝ` with
  nonzero period has a bound `B` with `|f t| ≤ B` for all `t`.
-/

public section

open Set

namespace Function

/-- A continuous periodic function `f : ℝ → ℝ` with nonzero period is bounded in absolute value:
there is a `B` with `|f t| ≤ B` for all `t`. -/
theorem Periodic.exists_forall_abs_le {f : ℝ → ℝ} {c : ℝ} (hp : Periodic f c) (hc : c ≠ 0)
    (hf : Continuous f) : ∃ B, ∀ t, |f t| ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hp.isBounded_of_continuous hc hf)
  exact ⟨B, fun t ↦ hB _ (mem_range_self t)⟩

end Function
