/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Continuity of `f t / t` for a function vanishing near zero

If `f` is continuous and vanishes in a neighbourhood of `0`, then the quotient `t ↦ f t / t` is
continuous: away from `0` it is a quotient by a nonzero continuous function, and near `0` it is
identically `0`.
-/

public section

open Filter
open scoped Topology

variable {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
  [ContinuousMul G₀] {f : G₀ → G₀}

/-- If `f` is continuous and vanishes near `0`, then `t ↦ f t / t` is continuous. -/
theorem Continuous.div_id_of_eventuallyEq_zero (hf : Continuous f) (h₀ : f =ᶠ[𝓝 0] 0) :
    Continuous fun t ↦ f t / t := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  rcases eq_or_ne t 0 with rfl | ht
  · refine (continuousAt_const (y := (0 : G₀))).congr (h₀.mono fun y hy ↦ ?_)
    rw [Pi.zero_apply] at hy
    simp [hy]
  · exact hf.continuousAt.div continuousAt_id ht
