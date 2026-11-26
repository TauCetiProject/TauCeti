/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Dynamics.Flow
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives along the trajectories of a flow

Let `ϕ` be a flow of `ℝ` on a topological space `α`. A *derivative of `g : α → F` along the flow*
at `y` is the derivative at time `0` of `t ↦ g (ϕ t y)`; for the flow of a vector field `V` on a
manifold and a differentiable function `g` it is `dg(V)`. Such derivatives can be read at every
point of a trajectory: the derivative of `s ↦ g (ϕ s x)` at time `t` is the derivative along the
flow at `ϕ t x` (`Flow.hasDerivAt_apply_flow_iff`), since the trajectory of `ϕ t x` is the
trajectory of `x` shifted in time by `t`.

## Main results

* `Flow.hasDerivAt_apply_flow_iff`: derivatives along a trajectory at any time.
-/

public section

namespace Flow

variable {α : Type*} [TopologicalSpace α] {ϕ : Flow ℝ α} {x : α}

/-- **Derivatives along a trajectory.** The derivative of `s ↦ g (ϕ s x)` at time `t` is the
derivative at time `0` of the same function along the trajectory of `ϕ t x`. -/
theorem hasDerivAt_apply_flow_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : α → F} {g' : F} {t : ℝ} :
    HasDerivAt (fun s ↦ g (ϕ s x)) g' t ↔ HasDerivAt (fun s ↦ g (ϕ s (ϕ t x))) g' 0 := by
  have hshift : (fun s ↦ g (ϕ s (ϕ t x))) = fun s ↦ g (ϕ (s + t) x) := by
    funext s
    rw [ϕ.map_add]
  rw [hshift]
  refine ⟨fun h ↦ HasDerivAt.comp_add_const 0 t (by rwa [zero_add]), fun h ↦ ?_⟩
  refine (HasDerivAt.comp_sub_const t t (by rwa [sub_self])).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s ↦ ?_)
  simp only [sub_add_cancel]

end Flow
