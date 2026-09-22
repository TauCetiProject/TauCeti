/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ExponentialDichotomy
public import TauCeti.Analysis.ODE.LyapunovPerron.Local

/-!
# Local stable and unstable sets at a Morse critical point

At a nondegenerate critical point `x` of a twice continuously differentiable function on a
finite-dimensional real Hilbert space, the negative-gradient vector field in displacement
coordinates splits as

`-hessianOperator f x z + negativeGradientRemainder f x (x + z)`.

The Hessian spectral splitting supplies a continuous projection onto the stable linear subspace
and exponential estimates for the linear term. The nonlinear remainder has arbitrarily small
Lipschitz constant on a sufficiently small ball. This file combines those facts with the local
Lyapunov--Perron theorem: the initial displacements of forward negative-gradient trajectories
confined to that ball form a Lipschitz graph over a ball in the stable linear subspace.

This is the Lipschitz local stable-manifold theorem specialized to a Morse critical point.
Differentiability of the graph map and its tangency to the stable linear subspace are not
established here.

Applying the same construction after reversing time gives the corresponding local unstable set
as a Lipschitz graph over the unstable Hessian spectral subspace.

## Main declaration

* `IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph`: confined forward
  trajectories in coordinates centred at a nondegenerate critical point form a Lipschitz graph
  over the stable Hessian spectral subspace.
* `IsNondegenerateCriticalPoint.exists_localUnstableSet_eq_lipschitzGraph`: the backward-time
  counterpart over the unstable Hessian spectral subspace.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
-/

public section

open Filter InnerProductSpace Metric Set Topology
open scoped Gradient NNReal

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

namespace IsNondegenerateCriticalPoint

/-- **Confined trajectories at a Morse critical point form a Lipschitz graph.** For every
positive Lipschitz constant `C`, there are positive radii `r` and `rho` such that the initial
displacements of forward solutions of the centred negative-gradient equation that remain in
`closedBall 0 r`, restricted by `norm (stableProjection z) ≤ rho`, are exactly the graph of a
`C`-Lipschitz map over `stableLinearSubspace ∩ closedBall 0 rho`.

The graph map vanishes at the origin, takes values in the unstable linear subspace (the kernel of
the stable projection), and depends only on the stable component of its input. The same radius
`r` also guarantees that every confined solution tends to zero. -/
theorem exists_localStableSet_eq_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      (∀ v, h.stableProjection (g v) = 0) ∧
      (∀ v, g (h.stableProjection v) = g v) ∧
      {z : E | ( ∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) ∧ y 0 = z ∧
            MapsTo y (Ici 0) (closedBall 0 r)) ∧
            ‖h.stableProjection z‖ ≤ rho} =
        (fun v ↦ v + g v) ''
          ((h.contDiffAt.stableLinearSubspace : Set E) ∩ closedBall 0 rho) ∧
      (∀ y : ℝ → E,
        IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) →
        MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) := by
  let P := h.stableProjection
  obtain ⟨K, alpha, hK, halpha, hs, hu⟩ :=
    h.exists_stableProjection_exponential_bounds
  let epsilon : ℝ≥0 := alpha * C / (8 * K * (K + C))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hsmall : 2 * K * (epsilon * 2) < alpha := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have hC' : (0 : ℝ) < C := by exact_mod_cast hC
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
      (A := -hessianOperator f x) (P := P) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localStableGraphMap
    (-hessianOperator f x) P N r hs hu hr.le hN hsmall
  let C₀ : ℝ≥0 :=
    2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))
  have hC₀ : C₀ ≤ C := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have hC' : (0 : ℝ) < C := by exact_mod_cast hC
    have hq : 2 * K * (epsilon * 2) / alpha < 1 :=
      (div_lt_one halpha).2 hsmall
    apply NNReal.coe_le_coe.1
    have heq : (C₀ : ℝ) = (C : ℝ) * K / (2 * K + C) := by
      dsimp only [C₀]
      push_cast [NNReal.coe_sub hq.le]
      dsimp only [epsilon]
      push_cast
      field_simp
      ring_nf
      have hden : (K : ℝ) * 8 + (C : ℝ) * 4 ≠ 0 := by positivity
      rw [← mul_inv_cancel₀ hden]
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K + C)).2
    nlinarith
  have hfield :
      (fun z ↦ (-hessianOperator f x) z + N z) = fun z ↦ (-∇ f) (x + z) := by
    funext z
    dsimp only [N]
    simpa only [add_sub_cancel_left, neg_apply] using
      (neg_gradient_eq_neg_hessianOperator_add_negativeGradientRemainder f x (x + z)).symm
  have hfield' : (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
      fun (_ : ℝ) z ↦ (-∇ f) (x + z) := by
    funext _
    exact hfield
  refine ⟨r, hr, rho, hrho, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : LipschitzWith C₀ g :=
      ContinuousLinearMap.lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall
    intro v w
    exact (hg v w).trans (by gcongr)
  · exact ContinuousLinearMap.localStableGraphMap_zero hs hu hr.le hN hsmall hN0
  · intro v
    exact ContinuousLinearMap.apply_localStableGraphMap hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection v
  · intro v
    exact ContinuousLinearMap.localStableGraphMap_map hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection v
  · have hrange : Set.range P = (h.contDiffAt.stableLinearSubspace : Set E) := by
      dsimp only [P]
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_stableProjection
    dsimp only [g]
    rw [hfield] at hset
    simpa only [hrange] using hset
  · intro y hy hmaps
    apply ContinuousLinearMap.tendsto_of_isIntegralCurveOn_mapsTo_closedBall
      hs hu hr.le hN hsmall hN0 h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection
    · rw [hfield']
      exact hy
    · exact hmaps

/-- **Confined backward trajectories at a Morse critical point form a Lipschitz graph.** For
every positive Lipschitz constant `C`, there are positive radii `r` and `rho` such that the
initial displacements of backward solutions of the centred negative-gradient equation that stay
in `closedBall 0 r`, restricted by `norm (unstableProjection z) ≤ rho`, are exactly the graph of
a `C`-Lipschitz map over `unstableLinearSubspace ∩ closedBall 0 rho`.

The graph map vanishes at the origin, takes values in the stable linear subspace (the kernel of
the unstable projection), and depends only on the unstable component of its input. Every such
confined backward solution tends to zero in backward time. -/
theorem exists_localUnstableSet_eq_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      (∀ v, h.unstableProjection (g v) = 0) ∧
      (∀ v, g (h.unstableProjection v) = g v) ∧
      {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) ∧ y 0 = z ∧
            MapsTo y (Iic 0) (closedBall 0 r)) ∧
            ‖h.unstableProjection z‖ ≤ rho} =
        (fun v ↦ v + g v) ''
          ((h.contDiffAt.unstableLinearSubspace : Set E) ∩ closedBall 0 rho) ∧
      (∀ y : ℝ → E,
        IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) →
        MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (nhds 0)) := by
  let P := h.stableProjection
  obtain ⟨K, alpha, hK, halpha, hs, hu⟩ :=
    h.exists_stableProjection_exponential_bounds
  let epsilon : ℝ≥0 := alpha * C / (8 * K * (K + C))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hsmall : 2 * K * (epsilon * 2) < alpha := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have hC' : (0 : ℝ) < C := by exact_mod_cast hC
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
    ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_mapsTo_closedBall_atBot_eq_image
      (A := -hessianOperator f x) (P := P) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localUnstableGraphMap
    (-hessianOperator f x) P N r hs hu hr.le hN hsmall
  let C₀ : ℝ≥0 :=
    2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))
  have hC₀ : C₀ ≤ C := by
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
    have hC' : (0 : ℝ) < C := by exact_mod_cast hC
    have hq : 2 * K * (epsilon * 2) / alpha < 1 :=
      (div_lt_one halpha).2 hsmall
    apply NNReal.coe_le_coe.1
    have heq : (C₀ : ℝ) = (C : ℝ) * K / (2 * K + C) := by
      dsimp only [C₀]
      push_cast [NNReal.coe_sub hq.le]
      dsimp only [epsilon]
      push_cast
      field_simp
      ring_nf
      have hden : (K : ℝ) * 8 + (C : ℝ) * 4 ≠ 0 := by positivity
      rw [← mul_inv_cancel₀ hden]
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K + C)).2
    nlinarith
  have hfield :
      (fun z ↦ (-hessianOperator f x) z + N z) = fun z ↦ (-∇ f) (x + z) := by
    funext z
    dsimp only [N]
    simpa only [add_sub_cancel_left, neg_apply] using
      (neg_gradient_eq_neg_hessianOperator_add_negativeGradientRemainder f x (x + z)).symm
  have hfield' : (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
      fun (_ : ℝ) z ↦ (-∇ f) (x + z) := by
    funext _
    exact hfield
  refine ⟨r, hr, rho, hrho, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : LipschitzWith C₀ g :=
      ContinuousLinearMap.lipschitzWith_localUnstableGraphMap hs hu hr.le hN hsmall
    intro v w
    exact (hg v w).trans (by gcongr)
  · exact ContinuousLinearMap.localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0
  · intro v
    simpa only [g, P, h.unstableProjection_eq_sub] using
      ContinuousLinearMap.sub_apply_localUnstableGraphMap hs hu hr.le hN hsmall
        h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection v
  · intro v
    simpa only [g, P, h.unstableProjection_eq_sub] using
      ContinuousLinearMap.localUnstableGraphMap_sub_apply hs hu hr.le hN hsmall
        h.isIdempotentElem_stableProjection v
  · have hrange : Set.range h.unstableProjection =
        (h.contDiffAt.unstableLinearSubspace : Set E) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_unstableProjection
    rw [hfield] at hset
    rw [← h.unstableProjection_eq_sub] at hset
    simpa only [g, P, hrange] using hset
  · intro y hy hmaps
    apply ContinuousLinearMap.tendsto_atBot_of_isIntegralCurveOn_mapsTo_closedBall
      hs hu hr.le hN hsmall hN0 h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection
    · rw [hfield']
      exact hy
    · exact hmaps

end IsNondegenerateCriticalPoint

end TauCeti

end
