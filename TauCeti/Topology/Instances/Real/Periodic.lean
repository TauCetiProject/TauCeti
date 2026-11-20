/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Bounds of continuous periodic functions on the real line

A continuous periodic function `f : ℝ → E` with nonzero period, valued in a seminormed group, is
bounded in norm.

## Main results

* `Function.Periodic.exists_forall_norm_le`: a continuous periodic function `f : ℝ → E` with
  nonzero period has a bound `B` with `‖f t‖ ≤ B` for all `t`.
-/

public section

open Set

namespace Function

/-- A continuous periodic function `f : ℝ → E` with nonzero period, valued in a seminormed group,
is bounded in norm: there is a `B` with `‖f t‖ ≤ B` for all `t`. -/
theorem Periodic.exists_forall_norm_le {E : Type*} [SeminormedAddGroup E] {f : ℝ → E} {c : ℝ}
    (hp : Periodic f c) (hc : c ≠ 0) (hf : Continuous f) : ∃ B, ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hp.isBounded_of_continuous hc hf)
  exact ⟨B, fun t ↦ hB _ (mem_range_self t)⟩

end Function
