/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.OrderClosed

/-!
# Boundaries of regular scalar superlevel sets

A continuous real-valued function whose derivative does not vanish on a level has that level
as the frontier of its strict superlevel set. This identifies the boundary of domains selected
by regular values without requiring a choice of normal vector field.
-/

public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {t : ℝ}

/-- The frontier of a strict superlevel set is its level set if the derivative is nonzero
everywhere on that level. -/
theorem Continuous.frontier_setOf_lt_eq_of_fderiv_ne_zero (hu : Continuous u)
    (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) :
    frontier {x | t < u x} = {x | u x = t} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (frontier_lt_subset_eq continuous_const hu hx).symm
  · intro x (hx : u x = t)
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, subset_closure (not_lt.mpr hx.le)⟩
    by_contra h
    rw [mem_closure_iff_frequently, not_frequently] at h
    have hmax : IsLocalMax u x := h.mono fun y hy ↦ by simpa [hx] using not_lt.1 hy
    exact hreg x hx hmax.fderiv_eq_zero
