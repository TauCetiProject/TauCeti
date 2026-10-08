/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.Convergence
public import TauCeti.Dynamics.Flow.Breaking
-- Private: used only to compare the gradient with the differential.
import TauCeti.Analysis.Calculus.Gradient

/-!
# Negative gradient trajectories break at nondegenerate critical points

A negative gradient trajectory trapped, in forward time, in a closed ball containing no critical
point other than its centre `x` converges to `x`; the same holds in backward time. So the radius of
such a ball isolates `x` in the sense of `TauCeti.Dynamics.Flow.Breaking`, and every sufficiently
small radius about a nondegenerate critical point does.

Feeding this into `Flow.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet` gives the
elementary step of the compactness theorem for spaces of Morse trajectories. If trajectories
converging to a critical point `q` accumulate on a trajectory converging instead to a nondegenerate
critical point `x ≠ q`, then they also accumulate on a nonconstant trajectory leaving `x`: the limit
is a trajectory broken at `x`. In terms of sets, the closure of the stable set `W^s(q)` meets the
unstable set `W^u(x)` on every small sphere about `x`. The time-reversed statement holds for
unstable sets.

## Main declarations

* `Flow.IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall` and
  `Flow.IsNegativeGradient.mem_unstableSet_of_forall_mem_closedBall`: a trajectory trapped in a
  closed ball whose only critical point is its centre converges to the centre.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_forall_mem_stableSet_of_forall_mem_closedBall`
  and its unstable counterpart: every small radius about a nondegenerate critical point isolates
  it.
* `TauCeti.IsNondegenerateCriticalPoint.eventually_exists_mem_closure_stableSet_inter_unstableSet`
  and its time reversal
  `TauCeti.IsNondegenerateCriticalPoint.eventually_exists_mem_closure_unstableSet_inter_stableSet`:
  limits of trajectories break at a nondegenerate critical point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories).
-/

public section

open Filter Metric Set Topology
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {x : E} {r : ℝ}

namespace Flow

/-- **A trajectory trapped near an isolated critical point converges to it.** If `f` is
differentiable with continuous gradient on `closedBall x r`, and `x` is the only critical point of
`f` in that ball, then a negative gradient trajectory staying in the ball at all nonnegative times
converges to `x`. -/
theorem IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall (hφ : IsNegativeGradient φ f)
    (hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) (closedBall x r)) (hcrit : ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x)
    {w : E} (hw : ∀ t, 0 ≤ t → φ t w ∈ closedBall x r) : w ∈ stableSet φ x := by
  obtain ⟨p, hp, hp0, hlim⟩ := TauCeti.IsIntegralCurveOn.exists_tendsto_atTop
    ((hφ.isIntegralCurve w).isIntegralCurveOn _) (isCompact_closedBall x r) hw hdiff hgrad
    ((finite_singleton x).subset fun y hy ↦ hcrit y hy.1 hy.2)
  exact mem_stableSet.2 (hcrit p hp hp0 ▸ hlim)

/-- **A trajectory trapped near an isolated critical point converges to it in backward time.** The
backward-time counterpart of `Flow.IsNegativeGradient.mem_stableSet_of_forall_mem_closedBall`. -/
theorem IsNegativeGradient.mem_unstableSet_of_forall_mem_closedBall (hφ : IsNegativeGradient φ f)
    (hdiff : ∀ y ∈ closedBall x r, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) (closedBall x r)) (hcrit : ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x)
    {w : E} (hw : ∀ t, t ≤ 0 → φ t w ∈ closedBall x r) : w ∈ unstableSet φ x := by
  obtain ⟨p, hp, hp0, hlim⟩ := TauCeti.IsIntegralCurveOn.exists_tendsto_atBot
    ((hφ.isIntegralCurve w).isIntegralCurveOn _) (isCompact_closedBall x r) hw hdiff hgrad
    ((finite_singleton x).subset fun y hy ↦ hcrit y hy.1 hy.2)
  exact mem_unstableSet.2 (hcrit p hp hp0 ▸ hlim)

end Flow

namespace TauCeti

namespace IsNondegenerateCriticalPoint

/-- Every small closed ball about a nondegenerate critical point carries the regularity used by the
convergence theorem and contains no other critical point. -/
private theorem eventually_closedBall (h : IsNondegenerateCriticalPoint f x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (∀ y ∈ closedBall x r, DifferentiableAt ℝ f y) ∧
      ContinuousOn (∇ f) (closedBall x r) ∧ ∀ y ∈ closedBall x r, ∇ f y = 0 → y = x := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((h.contDiffAt.eventually (by simp)).and
      (eventually_nhdsWithin_iff.1 h.eventually_fderiv_ne_zero))
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have hsub (y : E) (hy : y ∈ closedBall x r) : y ∈ ball x ε :=
    mem_ball.2 ((mem_closedBall.1 hy).trans_lt hr.2)
  have hgradfun : (∇ f : E → E) = fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y) := by
    funext y
    exact (InnerProductSpace.toDual ℝ E).eq_symm_apply.2 toDual_gradient
  refine ⟨fun y hy ↦ (hball y (hsub y hy)).1.differentiableAt (by simp), fun y hy ↦ ?_,
    fun y hy hy0 ↦ by_contra fun hyx ↦ (hball y (hsub y hy)).2 hyx ?_⟩
  · rw [hgradfun]
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
      ((hball y (hsub y hy)).1.continuousAt_fderiv two_ne_zero)).continuousWithinAt
  · rw [← norm_eq_zero, ← norm_gradient_eq_norm_fderiv, hy0, norm_zero]

/-- **Small balls isolate a nondegenerate critical point in forward time.** For every sufficiently
small `r > 0`, a negative gradient trajectory staying in `closedBall x r` at all nonnegative times
converges to the nondegenerate critical point `x`. -/
theorem eventually_forall_mem_stableSet_of_forall_mem_closedBall
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ w, (∀ t, 0 ≤ t → φ t w ∈ closedBall x r) → w ∈ Flow.stableSet φ x := by
  filter_upwards [h.eventually_closedBall] with r ⟨hdiff, hgrad, hcrit⟩ w hw
  exact hφ.mem_stableSet_of_forall_mem_closedBall hdiff hgrad hcrit hw

/-- **Small balls isolate a nondegenerate critical point in backward time.** For every
sufficiently small `r > 0`, a negative gradient trajectory staying in `closedBall x r` at all
nonpositive times converges to the nondegenerate critical point `x` in backward time. -/
theorem eventually_forall_mem_unstableSet_of_forall_mem_closedBall
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ w, (∀ t, t ≤ 0 → φ t w ∈ closedBall x r) → w ∈ Flow.unstableSet φ x := by
  filter_upwards [h.eventually_closedBall] with r ⟨hdiff, hgrad, hcrit⟩ w hw
  exact hφ.mem_unstableSet_of_forall_mem_closedBall hdiff hgrad hcrit hw

/-- **Limits of trajectories break at a nondegenerate critical point.** Let `x` be a nondegenerate
critical point and `q ≠ x`. If a point `y` of the stable set of `x` is a limit of points of the
stable set of `q`, then for every sufficiently small `r > 0` some point at distance `r` from `x`
lies both in the unstable set of `x` and in the closure of the stable set of `q`. -/
theorem eventually_exists_mem_closure_stableSet_inter_unstableSet
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) {q : E}
    (hqx : q ≠ x) {y : E} (hy : y ∈ closure (Flow.stableSet φ q) ∩ Flow.stableSet φ x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ z ∈ closure (Flow.stableSet φ q) ∩ Flow.unstableSet φ x, dist z x = r := by
  filter_upwards [self_mem_nhdsWithin,
    h.eventually_forall_mem_stableSet_of_forall_mem_closedBall hφ,
    h.eventually_forall_mem_unstableSet_of_forall_mem_closedBall hφ] with r hr hfwd hbwd
  exact Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet (mem_Ioi.1 hr)
    hfwd hbwd (Flow.isInvariant_stableSet φ q) (Flow.disjoint_stableSet hqx) hy

/-- **Limits of trajectories break at a nondegenerate critical point, in backward time.** Let `x` be
a nondegenerate critical point and `p ≠ x`. If a point `y` of the unstable set of `x` is a limit of
points of the unstable set of `p`, then for every sufficiently small `r > 0` some point at distance
`r` from `x` lies both in the stable set of `x` and in the closure of the unstable set of `p`. -/
theorem eventually_exists_mem_closure_unstableSet_inter_stableSet
    (h : IsNondegenerateCriticalPoint f x) (hφ : Flow.IsNegativeGradient φ f) {p : E}
    (hpx : p ≠ x) {y : E} (hy : y ∈ closure (Flow.unstableSet φ p) ∩ Flow.unstableSet φ x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ z ∈ closure (Flow.unstableSet φ p) ∩ Flow.stableSet φ x, dist z x = r := by
  filter_upwards [self_mem_nhdsWithin,
    h.eventually_forall_mem_stableSet_of_forall_mem_closedBall hφ,
    h.eventually_forall_mem_unstableSet_of_forall_mem_closedBall hφ] with r hr hfwd hbwd
  exact Flow.exists_mem_closure_inter_stableSet_of_mem_closure_inter_unstableSet (mem_Ioi.1 hr)
    hfwd hbwd (Flow.isInvariant_unstableSet φ p) (Flow.disjoint_unstableSet hpx) hy

end IsNondegenerateCriticalPoint

end TauCeti

end
