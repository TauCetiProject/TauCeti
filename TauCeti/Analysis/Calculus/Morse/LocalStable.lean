/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ExponentialDichotomy
public import TauCeti.Analysis.ODE.LyapunovPerron.Local

/-!
# The local stable set at a Morse critical point

At a nondegenerate critical point `x` of a twice continuously differentiable function on a
finite-dimensional real Hilbert space, the negative-gradient vector field in displacement
coordinates splits as

`-hessianOperator f x z + negativeGradientRemainder f x (x + z)`.

The Hessian spectral splitting supplies a continuous projection onto the stable linear subspace
and exponential estimates for the linear term. The nonlinear remainder has arbitrarily small
Lipschitz constant on a sufficiently small ball. This file combines those facts with the local
Lyapunov--Perron theorem: the initial displacements of forward negative-gradient trajectories
confined to that ball form a Lipschitz graph over a ball in the stable linear subspace.

This is the Lipschitz local stable-manifold theorem specialized to a Morse critical point. The
graph is not yet shown differentiable; differentiability with derivative zero at the origin is
the remaining step needed to identify the graph as a smooth submanifold tangent to the stable
linear subspace.

## Main declaration

* `TauCeti.IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph`: the local
  stable set in coordinates centred at a nondegenerate critical point is a Lipschitz graph over
  the stable Hessian spectral subspace.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
-/

public section

open Filter InnerProductSpace Metric Set
open scoped Gradient NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- **The local stable set at a Morse critical point is a Lipschitz graph.** There are positive
radii `r` and `rho` such that the initial displacements of forward solutions of the centred
negative-gradient equation that remain in `closedBall 0 r`, restricted by
`norm (stableProjection z) ≤ rho`, are exactly the graph of a Lipschitz map over
`stableLinearSubspace ∩ closedBall 0 rho`.

The graph map vanishes at the origin, takes values in the unstable linear subspace (the kernel of
the stable projection), and depends only on the stable component of its input. Every confined
solution tends to zero by
`ContinuousLinearMap.tendsto_of_isIntegralCurveOn_mapsTo_closedBall`. -/
theorem IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) :
    ∃ r > 0, ∃ rho > 0, ∃ (g : E → E) (C : ℝ≥0),
      LipschitzWith C g ∧ g 0 = 0 ∧
      (∀ v, h.stableProjection (g v) = 0) ∧
      (∀ v, g (h.stableProjection v) = g v) ∧
      {z : E | ( ∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) ∧ y 0 = z ∧
            MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖h.stableProjection z‖ ≤ rho} =
        (fun v ↦ v + g v) ''
          ((h.contDiffAt.stableLinearSubspace : Set E) ∩ closedBall 0 rho) := by
  obtain ⟨K, alpha, hK, halpha, hs, hu⟩ := h.exists_stableProjection_exponential_bounds
  let epsilon : ℝ≥0 := alpha / (8 * K)
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hsmall : 2 * K * (epsilon * 2) < alpha := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have hsmall' : (2 : ℝ) * K * (((epsilon : ℝ≥0) : ℝ) * 2) < alpha := by
      dsimp only [epsilon]
      push_cast
      field_simp
      nlinarith
    exact_mod_cast hsmall'
  obtain ⟨r, hr, hrem⟩ :=
    h.contDiffAt.exists_lipschitzOnWith_negativeGradientRemainder epsilon hepsilon
  let N : E → E := fun z ↦ negativeGradientRemainder f x (x + z)
  have hN : LipschitzOnWith epsilon N (closedBall 0 r) := by
    intro z hz w hw
    have hz' : x + z ∈ closedBall x r := by
      simpa only [mem_closedBall, ← dist_add_left x z 0, add_zero] using hz
    have hw' : x + w ∈ closedBall x r := by
      simpa only [mem_closedBall, ← dist_add_left x w 0, add_zero] using hw
    dsimp only [N]
    simpa only [edist_dist, dist_add_left] using hrem hz' hw'
  have hN0 : N 0 = 0 := by
    simp only [N, add_zero, negativeGradientRemainder_self h.gradient_eq_zero]
  obtain ⟨rho, hrho, hset⟩ :=
    ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image
      (A := -hessianOperator f x) (P := h.stableProjection) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localStableGraphMap
    (-hessianOperator f x) h.stableProjection N r hs hu hr.le hN hsmall
  let C : ℝ≥0 :=
    2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))
  refine ⟨r, hr, rho, hrho, g, C, ?_, ?_, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall
  · exact ContinuousLinearMap.localStableGraphMap_zero hs hu hr.le hN hsmall hN0
  · intro v
    exact ContinuousLinearMap.apply_localStableGraphMap hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection v
  · intro v
    exact ContinuousLinearMap.localStableGraphMap_map hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection v
  · have hfield :
      (fun z ↦ (-hessianOperator f x) z + N z) = fun z ↦ (-∇ f) (x + z) := by
      funext z
      dsimp only [N]
      simpa only [add_sub_cancel_left, neg_apply] using
        (neg_gradient_eq_neg_hessianOperator_add_negativeGradientRemainder f x (x + z)).symm
    have hrange : Set.range h.stableProjection =
        (h.contDiffAt.stableLinearSubspace : Set E) := by
      rw [← h.range_stableProjection]
      rfl
    dsimp only [g]
    rw [hfield] at hset
    simpa only [hrange] using hset

end TauCeti

end
