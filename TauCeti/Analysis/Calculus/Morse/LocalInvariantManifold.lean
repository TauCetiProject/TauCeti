/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ExponentialDichotomy
public import TauCeti.Analysis.ODE.LyapunovPerron.Local

/-!
# Local invariant sets at a Morse critical point

At a nondegenerate critical point `x` of a twice continuously differentiable function on a
finite-dimensional real Hilbert space, the negative-gradient vector field in displacement
coordinates splits as

`-hessianOperator f x z + negativeGradientRemainder f x (x + z)`.

The Hessian spectral splitting supplies a continuous projection onto the stable linear subspace
and exponential estimates for the linear term. The nonlinear remainder has arbitrarily small
Lipschitz constant on a sufficiently small ball. This file combines those facts with the local
Lyapunov--Perron theorem: the initial displacements of forward negative-gradient trajectories
confined to that ball form a Lipschitz graph over a ball in the stable linear subspace.

This is a local stable-set graph and tangency theorem at the equilibrium: the graph map is
Lipschitz, differentiable at the origin with derivative zero, and hence tangent there to the stable
linear subspace. Smoothness away from the equilibrium and the resulting embedded-submanifold
structure are not established here.

Applying the same construction after reversing time gives the corresponding local unstable set
as a Lipschitz graph over the unstable Hessian spectral subspace.

## Main declarations

* `IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph`: confined forward
  trajectories in coordinates centred at a nondegenerate critical point form a Lipschitz graph,
  tangent at the origin to the stable Hessian spectral subspace.
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

/-- The nonlinear remainder of the centred negative-gradient field fixes the origin. -/
private theorem negativeGradientRemainder_centered_zero (h : IsNondegenerateCriticalPoint f x) :
    (fun z ↦ negativeGradientRemainder f x (x + z)) 0 = 0 := by
  simp only [add_zero, negativeGradientRemainder_self h.gradient_eq_zero]

/-- In displacement coordinates the negative-gradient field is the linearization
`-hessianOperator f x` plus the nonlinear remainder. -/
private theorem neg_gradient_centered_eq :
    (fun z ↦ (-hessianOperator f x) z + negativeGradientRemainder f x (x + z)) =
      fun z ↦ (-∇ f) (x + z) := by
  funext z
  simpa only [add_sub_cancel_left, neg_apply] using
    (neg_gradient_eq_neg_hessianOperator_add_negativeGradientRemainder f x (x + z)).symm

/-- **The Lyapunov--Perron data of a Morse critical point.** For every positive `C` there are
exponential dichotomy constants `K`, `alpha` for the linearization `-hessianOperator f x` along
the stable projection, and a radius `r` on which the nonlinear remainder of the centred
negative-gradient field is Lipschitz with a constant `epsilon` small enough both for the
Lyapunov--Perron machinery and to make the resulting graph constant at most `C`.

This is the setup shared by `IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph`
and `IsNondegenerateCriticalPoint.exists_localUnstableSet_eq_lipschitzGraph`. -/
private theorem exists_lyapunovPerronData (h : IsNondegenerateCriticalPoint f x) (C : ℝ≥0)
    (hC : 0 < C) :
    ∃ (K alpha epsilon : ℝ≥0) (r : ℝ), 0 < r ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (h.stableProjection v)‖ ≤
          K * Real.exp (-alpha * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E,
        ‖NormedSpace.exp (t • (-hessianOperator f x)) (v - h.stableProjection v)‖ ≤
          K * Real.exp (alpha * t) * ‖v‖) ∧
      LipschitzOnWith epsilon (fun z ↦ negativeGradientRemainder f x (x + z)) (closedBall 0 r) ∧
      2 * K * (epsilon * 2) < alpha ∧
      2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha)) ≤ C := by
  obtain ⟨K, alpha, hK, halpha, hs, hu⟩ := h.exists_stableProjection_exponential_bounds
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have halpha' : (0 : ℝ) < alpha := by exact_mod_cast halpha
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  let epsilon : ℝ≥0 := alpha * C / (8 * K * (K + C))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hsmall : 2 * K * (epsilon * 2) < alpha := by
    have hsmall' : (2 : ℝ) * K * (((epsilon : ℝ≥0) : ℝ) * 2) < alpha := by
      dsimp only [epsilon]
      push_cast
      field_simp
      nlinarith
    exact_mod_cast hsmall'
  obtain ⟨r, hr, hrem⟩ :=
    h.contDiffAt.exists_lipschitzOnWith_negativeGradientRemainder epsilon hepsilon
  refine ⟨K, alpha, epsilon, r, hr, hs, hu, ?_, hsmall, ?_⟩
  · intro z hz w hw
    have hz' : x + z ∈ closedBall x r := by
      simpa only [mem_closedBall, ← dist_add_left x z 0, add_zero] using hz
    have hw' : x + w ∈ closedBall x r := by
      simpa only [mem_closedBall, ← dist_add_left x w 0, add_zero] using hw
    simpa only [edist_dist, dist_add_left] using hrem hz' hw'
  · have hq : 2 * K * (epsilon * 2) / alpha < 1 := (div_lt_one halpha).2 hsmall
    apply NNReal.coe_le_coe.1
    have heq : ((2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha)) :
        ℝ≥0) : ℝ) = (C : ℝ) * K / (2 * K + C) := by
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

/-- **Confined trajectories at a Morse critical point form a Lipschitz graph.** For every
positive Lipschitz constant `C`, there are positive radii `r` and `rho` such that the initial
displacements of forward solutions of the centred negative-gradient equation that remain in
`closedBall 0 r`, restricted by `norm (stableProjection z) ≤ rho`, are exactly the graph of a
`C`-Lipschitz map over `stableLinearSubspace ∩ closedBall 0 rho`.

The graph map vanishes at the origin, has derivative zero there, takes values in the unstable
linear subspace (the kernel of the stable projection), and depends only on the stable component of
its input. Thus its graph is tangent at the origin to the stable linear subspace. The same radius
`r` also guarantees that every confined solution tends to zero. -/
theorem exists_localStableSet_eq_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
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
  obtain ⟨K, alpha, epsilon, r, hr, hs, hu, hN, hsmall, hC₀⟩ := h.exists_lyapunovPerronData C hC
  set N : E → E := fun z ↦ negativeGradientRemainder f x (x + z) with hNdef
  have hN0 : N 0 = 0 := by
    rw [hNdef]
    exact h.negativeGradientRemainder_centered_zero
  have hN' : HasFDerivAt N (0 : E →L[ℝ] E) 0 := by
    have hshift : HasFDerivAt (fun z : E ↦ x + z) (ContinuousLinearMap.id ℝ E) 0 :=
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E))).const_add x
    have houter : HasFDerivAt (negativeGradientRemainder f x) (0 : E →L[ℝ] E) (x + 0) := by
      simpa only [add_zero] using h.contDiffAt.hasFDerivAt_negativeGradientRemainder
    have hcomp := (houter.comp 0 hshift).congr_fderiv (ContinuousLinearMap.zero_comp _)
    simpa only [hNdef, Function.comp_def] using hcomp
  have hfield : (fun z ↦ (-hessianOperator f x) z + N z) = fun z ↦ (-∇ f) (x + z) := by
    rw [hNdef]
    exact neg_gradient_centered_eq
  have hfield_time :
      (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
        fun (_ : ℝ) z ↦ (-∇ f) (x + z) :=
    congrArg (fun F : E → E ↦ fun (_ : ℝ) ↦ F) hfield
  obtain ⟨rho, hrho, hset⟩ :=
    ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image
      (A := -hessianOperator f x) (P := h.stableProjection) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localStableGraphMap
    (-hessianOperator f x) h.stableProjection N r hs hu hr.le hN hsmall
  refine ⟨r, hr, rho, hrho, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : LipschitzWith
        (2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))) g :=
      ContinuousLinearMap.lipschitzWith_localStableGraphMap hs hu hr.le hN hsmall
    intro v w
    exact (hg v w).trans (by gcongr)
  · exact ContinuousLinearMap.localStableGraphMap_zero hs hu hr.le hN hsmall hN0
  · exact ContinuousLinearMap.hasFDerivAt_localStableGraphMap_zero hs hu hr.le hN hsmall hr hN0 hN'
  · intro v
    exact ContinuousLinearMap.apply_localStableGraphMap hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection v
  · intro v
    exact ContinuousLinearMap.localStableGraphMap_map hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection v
  · have hrange : Set.range (h.stableProjection : E → E) =
        (h.contDiffAt.stableLinearSubspace : Set E) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_stableProjection
    dsimp only [g]
    rw [hfield_time] at hset
    simpa only [hrange] using hset
  · intro y hy hmaps
    apply ContinuousLinearMap.tendsto_of_isIntegralCurveOn_mapsTo_closedBall
      hs hu hr.le hN hsmall hN0 h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection
    · rw [hfield_time]
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
  obtain ⟨K, alpha, epsilon, r, hr, hs, hu, hN, hsmall, hC₀⟩ := h.exists_lyapunovPerronData C hC
  set N : E → E := fun z ↦ negativeGradientRemainder f x (x + z) with hNdef
  have hN0 : N 0 = 0 := by
    rw [hNdef]
    exact h.negativeGradientRemainder_centered_zero
  have hfield : (fun z ↦ (-hessianOperator f x) z + N z) = fun z ↦ (-∇ f) (x + z) := by
    rw [hNdef]
    exact neg_gradient_centered_eq
  have hfield_time :
      (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
        fun (_ : ℝ) z ↦ (-∇ f) (x + z) :=
    congrArg (fun F : E → E ↦ fun (_ : ℝ) ↦ F) hfield
  obtain ⟨rho, hrho, hset⟩ :=
    ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image
      (A := -hessianOperator f x) (P := h.stableProjection) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localUnstableGraphMap
    (-hessianOperator f x) h.stableProjection N r hs hu hr.le hN hsmall
  refine ⟨r, hr, rho, hrho, g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : LipschitzWith
        (2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))) g :=
      ContinuousLinearMap.lipschitzWith_localUnstableGraphMap hs hu hr.le hN hsmall
    intro v w
    exact (hg v w).trans (by gcongr)
  · exact ContinuousLinearMap.localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0
  · intro v
    have hgP := ContinuousLinearMap.apply_localUnstableGraphMap hs hu hr.le hN hsmall
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection v
    simpa only [g, h.unstableProjection_apply, sub_eq_zero] using hgP.symm
  · intro v
    simpa only [g, h.unstableProjection_apply] using
      ContinuousLinearMap.localUnstableGraphMap_sub_map hs hu hr.le hN hsmall
        h.isIdempotentElem_stableProjection v
  · have hrange : Set.range (h.unstableProjection : E → E) =
        (h.contDiffAt.unstableLinearSubspace : Set E) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_unstableProjection
    rw [hfield_time] at hset
    rw [← h.unstableProjection_def] at hset
    simpa only [g, hrange] using hset
  · intro y hy hmaps
    apply ContinuousLinearMap.tendsto_atBot_of_isIntegralCurveOn_mapsTo_closedBall
      hs hu hr.le hN hsmall hN0 h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection
    · rw [hfield_time]
      exact hy
    · exact hmaps

end IsNondegenerateCriticalPoint

end TauCeti

end
