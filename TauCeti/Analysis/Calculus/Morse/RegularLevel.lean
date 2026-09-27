/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.Stable
import Mathlib.Algebra.Module.LinearMap.DivisionRing

/-!
# Regular levels along connecting gradient trajectories

For a locally unique negative-gradient flow, a trajectory joining distinct limiting points
never meets a critical point. Hence every point on such a trajectory is a regular point of the
defining function. In particular, the intermediate level used to slice the time-translation
action is regular at every connecting point on that level.

The Lipschitz hypothesis on the gradient supplies uniqueness of trajectories. It matters:
without uniqueness, a differentiable orbit of a non-Lipschitz vector field may pass through a
rest point and continue. This regularity is the differential input for giving the level slice
the smooth structure used in Morse trajectory spaces.

The trajectory-space construction follows M. Audin and M. Damian,
*Morse Theory and Floer Homology*, Chapter 2.
-/

public section

open InnerProductSpace Set
open scoped Gradient NNReal

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E} {K : ℝ≥0}

/-- A connecting orbit between distinct endpoints contains no critical point when the gradient
field is Lipschitz. If it met one, uniqueness would make the entire orbit constant. -/
theorem IsNegativeGradient.gradient_ne_zero_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : LipschitzWith K (∇ f)) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    ∇ f x ≠ 0 := by
  intro hzero
  have hfixed : ∀ t, φ t x = x := by
    intro t
    calc
      φ t x = TauCeti.negativeGradientFlow f hf t x := by
        simpa using (TauCeti.eq_negativeGradientFlow f hf (hφ.isIntegralCurve x) t)
      _ = x := (TauCeti.forall_negativeGradientFlow_eq_self_iff f hf x).2 hzero t
  have hxp : x = p := tendsto_nhds_unique tendsto_const_nhds (by
    simpa only [hfixed] using (mem_unstableSet.mp hx.1))
  have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds (by
    simpa only [hfixed] using (mem_stableSet.mp hx.2))
  exact hpq (hxp.symm.trans hxq)

/-- Every point of a connecting orbit between distinct endpoints is a differentiability point
of the potential when its totalized gradient is Lipschitz. -/
theorem IsNegativeGradient.differentiableAt_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : LipschitzWith K (∇ f)) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    DifferentiableAt ℝ f x := by
  by_contra hdiff
  exact (hφ.gradient_ne_zero_of_mem_unstableSet_inter_stableSet hf hpq hx)
    (gradient_eq_zero_of_not_differentiableAt hdiff)

/-- The derivative of the potential is surjective at every point on a connecting orbit between
distinct endpoints. Thus each intermediate level is regular along the connecting set. -/
theorem IsNegativeGradient.surjective_fderiv_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : LipschitzWith K (∇ f)) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    Function.Surjective (fderiv ℝ f x) := by
  apply LinearMap.surjective_iff_ne_zero.mpr
  intro hderiv
  apply hφ.gradient_ne_zero_of_mem_unstableSet_inter_stableSet hf hpq hx
  apply (toDual ℝ E).injective
  apply ContinuousLinearMap.ext
  intro y
  have hy := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L y) hderiv
  simpa [toDual_gradient] using hy

end Flow

end
