/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Bounds for continuous periodic functions on `ℝ`

A continuous periodic function on `ℝ` with values in a seminormed group has bounded norm
(`Function.Periodic.exists_bound_of_continuous`). This is the pointwise form of Mathlib's
`Function.Periodic.isBounded_of_continuous`, which bounds the range instead, and is the form needed
to bound period-one Hamiltonians and their normalizations in Floer theory.
-/

public section

open Set

namespace Function

/-- A continuous periodic function on `ℝ` has bounded norm. -/
theorem Periodic.exists_bound_of_continuous {E : Type*} [SeminormedAddGroup E] {f : ℝ → E}
    {c : ℝ} (hf : Periodic f c) (hc : c ≠ 0) (hfc : Continuous f) : ∃ C, ∀ t, ‖f t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hf.isBounded_of_continuous hc hfc)
  exact ⟨C, fun t ↦ hC _ (mem_range_self t)⟩

end Function
