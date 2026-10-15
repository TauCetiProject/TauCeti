/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ConnectingOrbit
public import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Regular levels along connecting gradient trajectories

For a flow in which critical points of the potential are rest points, a trajectory joining
distinct limiting points never meets a critical point. Hence every point on such a trajectory is a
regular point of the defining function. In particular, the intermediate level used to slice the
time-translation action is regular at every connecting point on that level.

The rest-point hypothesis follows from uniqueness of trajectories, for example when the gradient
is Lipschitz. Without uniqueness, a differentiable orbit of a non-Lipschitz vector field may pass
through a rest point and continue. This regularity is the differential input for giving the level
slice the smooth structure used in Morse trajectory spaces.

The trajectory-space construction follows M. Audin and M. Damian,
*Morse Theory and Floer Homology*, Chapter 2.
-/

public section

open InnerProductSpace Set
open scoped Gradient

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E}

/-- A connecting orbit between distinct endpoints contains no critical point when the gradient
vanishes only at rest points. If it met one, the entire orbit would be constant. -/
theorem gradient_ne_zero_of_mem_unstableSet_inter_stableSet
    (hrest : ∀ y, ∇ f y = 0 → ∀ t, φ t y = y) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    ∇ f x ≠ 0 := by
  intro hzero
  have hfixed := hrest x hzero
  have hinj := orbit_injective_of_ne_of_mem_unstableSet_inter_stableSet hpq hx
  have h01 : (0 : ℝ) = 1 := hinj (by simp [hfixed])
  exact zero_ne_one h01

/-- Every point of a connecting orbit between distinct endpoints is a differentiability point
of the potential when critical points are rest points. -/
theorem differentiableAt_of_mem_unstableSet_inter_stableSet
    (hrest : ∀ y, ∇ f y = 0 → ∀ t, φ t y = y) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    DifferentiableAt ℝ f x := by
  by_contra hdiff
  exact (gradient_ne_zero_of_mem_unstableSet_inter_stableSet hrest hpq hx)
    (gradient_eq_zero_of_not_differentiableAt hdiff)

/-- The derivative of the potential is surjective at every point on a connecting orbit between
distinct endpoints. Thus each intermediate level is regular along the connecting set. -/
theorem fderiv_surjective_of_mem_unstableSet_inter_stableSet
    (hrest : ∀ y, ∇ f y = 0 → ∀ t, φ t y = y) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    Function.Surjective (fderiv ℝ f x) := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro hderiv
  apply gradient_ne_zero_of_mem_unstableSet_inter_stableSet hrest hpq hx
  have hderiv' : fderiv ℝ f x = 0 := by
    exact_mod_cast hderiv
  apply norm_eq_zero.mp
  rw [TauCeti.norm_gradient_eq_norm_fderiv, hderiv']
  simp

end Flow

end
