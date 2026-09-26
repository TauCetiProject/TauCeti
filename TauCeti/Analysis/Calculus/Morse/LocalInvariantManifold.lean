/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ExponentialDichotomy
public import TauCeti.Analysis.InnerProductSpace.EuclideanClosedBall
public import TauCeti.Analysis.ODE.LyapunovPerron.Embedding
import Mathlib.Analysis.ODE.Transform

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
as a Lipschitz graph tangent at the origin to the unstable Hessian spectral subspace.

Because the projection inverts the graph parameterization, each of the two sets is homeomorphic to
a closed ball in the spectral subspace it is a graph over, hence to a Euclidean closed ball of the
dimension of that subspace. This is where the Morse index acquires its geometric meaning: the
local unstable set is a disk of dimension the Morse index, and the local stable set a disk of
complementary dimension. At the two extreme indices one of the disks is a single point: the zero
displacement, which is the critical point `x` in these centred coordinates and, as soon as both
radii are nonnegative, belongs to both sets.

## Main declarations

* `localInvariantSet`: the displacements from which a solution of the centred negative-gradient
  equation stays in a given ball throughout a given time set, truncated by a norm bound on a
  projection, together with its forward and backward instances at a nondegenerate critical point,
  `IsNondegenerateCriticalPoint.localStableSet` and
  `IsNondegenerateCriticalPoint.localUnstableSet`.
* `IsNondegenerateCriticalPoint.exists_localStableSet_eq_lipschitzGraph`: confined forward
  trajectories in coordinates centred at a nondegenerate critical point form a Lipschitz graph,
  tangent at the origin to the stable Hessian spectral subspace.
* `IsNondegenerateCriticalPoint.exists_localUnstableSet_eq_lipschitzGraph`: the backward-time
  counterpart, tangent at the origin to the unstable Hessian spectral subspace.
* `IsNondegenerateCriticalPoint.exists_localStableSet_homeomorph_closedBall` and
  `IsNondegenerateCriticalPoint.exists_localUnstableSet_homeomorph_closedBall`: the two sets are
  closed disks of dimension the ambient dimension minus the Morse index, respectively the Morse
  index.
* `zero_mem_localInvariantSet`, with `IsNondegenerateCriticalPoint.zero_mem_localStableSet` and
  `IsNondegenerateCriticalPoint.zero_mem_localUnstableSet`: every such set with nonnegative radii
  contains the zero displacement, which is the critical point `x` in centred coordinates.
* `IsNondegenerateCriticalPoint.exists_localUnstableSet_eq_singleton_of_morseIndex_eq_zero` and
  `IsNondegenerateCriticalPoint.exists_localStableSet_eq_singleton_of_morseIndex_eq_finrank`: at a
  local minimum, respectively a local maximum, the degenerate one of the two disks is exactly the
  zero displacement.

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {x : E}

section

variable [CompleteSpace E]

/-- The displacements `z` from which the centred negative-gradient equation `z' = (-∇ f) (x + z)`
has a solution staying in `closedBall 0 r` for all times in `s`, truncated by the bound
`‖Q z‖ ≤ rho`. The local stable and unstable sets at a nondegenerate critical point are the two
instances of this set that the Lyapunov--Perron construction describes. -/
def localInvariantSet (f : E → ℝ) (x : E) (s : Set ℝ) (Q : E →L[ℝ] E) (r rho : ℝ) : Set E :=
  {z : E | (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) s ∧ y 0 = z ∧
      MapsTo y s (closedBall 0 r)) ∧ ‖Q z‖ ≤ rho}

@[simp]
theorem mem_localInvariantSet {s : Set ℝ} {Q : E →L[ℝ] E} {r rho : ℝ} {z : E} :
    z ∈ localInvariantSet f x s Q r rho ↔
      (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) s ∧ y 0 = z ∧
        MapsTo y s (closedBall 0 r)) ∧ ‖Q z‖ ≤ rho :=
  Iff.rfl

/-- At a critical point the zero displacement belongs to every such set with nonnegative radii,
whatever the time set and the projection: the constant displacement trajectory `y = 0`, which
represents the equilibrium at `x`, solves the centred equation and stays in every ball of
nonnegative radius. -/
theorem zero_mem_localInvariantSet (hx : ∇ f x = 0) (s : Set ℝ) (Q : E →L[ℝ] E) {r rho : ℝ}
    (hr : 0 ≤ r) (hrho : 0 ≤ rho) : (0 : E) ∈ localInvariantSet f x s Q r rho :=
  ⟨⟨fun _ ↦ 0, (isIntegralCurve_const fun _ ↦ by simp [hx]).isIntegralCurveOn _, rfl,
    fun _ _ ↦ by simpa using hr⟩, by simpa using hrho⟩

end

variable [FiniteDimensional ℝ E]

namespace IsNondegenerateCriticalPoint

/-- The local stable set at a nondegenerate critical point: the displacements from which the
centred negative-gradient equation has a forward solution staying in `closedBall 0 r`, truncated
by the bound `‖stableProjection z‖ ≤ rho`. -/
def localStableSet (h : IsNondegenerateCriticalPoint f x) (r rho : ℝ) : Set E :=
  localInvariantSet f x (Ici 0) h.stableProjection r rho

/-- The local unstable set at a nondegenerate critical point: the displacements from which the
centred negative-gradient equation has a backward solution staying in `closedBall 0 r`, truncated
by the bound `‖unstableProjection z‖ ≤ rho`. -/
def localUnstableSet (h : IsNondegenerateCriticalPoint f x) (r rho : ℝ) : Set E :=
  localInvariantSet f x (Iic 0) h.unstableProjection r rho

@[simp]
theorem mem_localStableSet {h : IsNondegenerateCriticalPoint f x} {r rho : ℝ} {z : E} :
    z ∈ h.localStableSet r rho ↔
      (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Ici 0) ∧ y 0 = z ∧
        MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖h.stableProjection z‖ ≤ rho :=
  Iff.rfl

@[simp]
theorem mem_localUnstableSet {h : IsNondegenerateCriticalPoint f x} {r rho : ℝ} {z : E} :
    z ∈ h.localUnstableSet r rho ↔
      (∃ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ (-∇ f) (x + w)) (Iic 0) ∧ y 0 = z ∧
        MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖h.unstableProjection z‖ ≤ rho :=
  Iff.rfl

/-- The nonlinear remainder of the centred negative-gradient field fixes the origin. -/
private theorem negativeGradientRemainder_centered_zero (h : IsNondegenerateCriticalPoint f x) :
    (fun z ↦ negativeGradientRemainder f x (x + z)) 0 = 0 := by
  simp only [add_zero, negativeGradientRemainder_self h.gradient_eq_zero]

/-- The nonlinear remainder of the centred negative-gradient field has derivative zero at the
origin. -/
private theorem hasFDerivAt_negativeGradientRemainder_centered
    (h : IsNondegenerateCriticalPoint f x) :
    HasFDerivAt (fun z ↦ negativeGradientRemainder f x (x + z)) (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_comp_add_left]
  simpa only [add_zero] using h.contDiffAt.hasFDerivAt_negativeGradientRemainder

/-- In displacement coordinates the negative-gradient field is the linearization
`-hessianOperator f x` plus the nonlinear remainder. -/
private theorem neg_gradient_centered_eq :
    (fun z ↦ (-hessianOperator f x) z + negativeGradientRemainder f x (x + z)) =
      fun z ↦ (-∇ f) (x + z) := by
  funext z
  simpa only [add_sub_cancel_left, neg_apply] using
    (neg_gradient_eq_neg_hessianOperator_add_negativeGradientRemainder f x (x + z)).symm

/-- The same splitting, read as the time-independent vector field the integral-curve API takes. -/
private theorem neg_gradient_centered_time_eq :
    (fun (_ : ℝ) (z : E) ↦
        (-hessianOperator f x) z + negativeGradientRemainder f x (x + z)) =
      fun (_ : ℝ) z ↦ (-∇ f) (x + z) :=
  congrArg (fun F : E → E ↦ fun (_ : ℝ) ↦ F) neg_gradient_centered_eq

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
      h.localStableSet r rho =
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
    rw [hNdef]
    exact h.hasFDerivAt_negativeGradientRemainder_centered
  have hfield_time :
      (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
        fun (_ : ℝ) z ↦ (-∇ f) (x + z) := by
    rw [hNdef]
    exact neg_gradient_centered_time_eq
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
    simpa only [localStableSet, localInvariantSet, hrange] using hset
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

The graph map vanishes at the origin, has derivative zero there, takes values in the stable linear
subspace (the kernel of the unstable projection), and depends only on the unstable component of
its input. Thus its graph is tangent at the origin to the unstable linear subspace. Every such
confined backward solution tends to zero in backward time. -/
theorem exists_localUnstableSet_eq_lipschitzGraph
    (h : IsNondegenerateCriticalPoint f x) (C : ℝ≥0) (hC : 0 < C) :
    ∃ r > 0, ∃ rho > 0, ∃ g : E → E,
      LipschitzWith C g ∧ g 0 = 0 ∧
      HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
      (∀ v, h.unstableProjection (g v) = 0) ∧
      (∀ v, g (h.unstableProjection v) = g v) ∧
      h.localUnstableSet r rho =
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
  have hN' : HasFDerivAt N (0 : E →L[ℝ] E) 0 := by
    rw [hNdef]
    exact h.hasFDerivAt_negativeGradientRemainder_centered
  have hfield_time :
      (fun (_ : ℝ) z ↦ (-hessianOperator f x) z + N z) =
        fun (_ : ℝ) z ↦ (-∇ f) (x + z) := by
    rw [hNdef]
    exact neg_gradient_centered_time_eq
  obtain ⟨rho, hrho, hset⟩ :=
    ContinuousLinearMap.exists_setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image
      (A := -hessianOperator f x) (P := h.stableProjection) (N := N)
      (K := K) (α := alpha) (ε := epsilon) hs hu hN hsmall hN0
      h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  let g : E → E := ContinuousLinearMap.localUnstableGraphMap
    (-hessianOperator f x) h.stableProjection N r hs hu hr.le hN hsmall
  refine ⟨r, hr, rho, hrho, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hg : LipschitzWith
        (2 * K * (epsilon * 2) / alpha * (K / (1 - 2 * K * (epsilon * 2) / alpha))) g :=
      ContinuousLinearMap.lipschitzWith_localUnstableGraphMap hs hu hr.le hN hsmall
    intro v w
    exact (hg v w).trans (by gcongr)
  · exact ContinuousLinearMap.localUnstableGraphMap_zero hs hu hr.le hN hsmall hN0
  · exact ContinuousLinearMap.hasFDerivAt_localUnstableGraphMap_zero
      hs hu hr.le hN hsmall hr hN0 hN'
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
    simpa only [g, localUnstableSet, localInvariantSet, hrange] using hset
  · intro y hy hmaps
    apply ContinuousLinearMap.tendsto_atBot_of_isIntegralCurveOn_mapsTo_closedBall
      hs hu hr.le hN hsmall hN0 h.isIdempotentElem_stableProjection
      h.commute_neg_hessianOperator_stableProjection
    · rw [hfield_time]
      exact hy
    · exact hmaps

/-- **The local stable set at a Morse critical point is a closed disk whose dimension is the
ambient dimension less the Morse index.** For suitable radii `r` and `rho`, the initial
displacements of forward negative-gradient solutions confined to `closedBall 0 r` and restricted
by `norm (stableProjection z) ≤ rho` are homeomorphic to a closed ball of that dimension. -/
theorem exists_localStableSet_homeomorph_closedBall (h : IsNondegenerateCriticalPoint f x) :
    ∃ r > 0, ∃ rho > 0, Nonempty (h.localStableSet r rho ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - morseIndex f x))) rho) := by
  obtain ⟨K, alpha, epsilon, r, hr, hs, hu, hN, hsmall, -⟩ := h.exists_lyapunovPerronData 1 one_pos
  obtain ⟨rho, hrho, ⟨e⟩⟩ := ContinuousLinearMap.exists_localStableSetHomeomorph
    (-hessianOperator f x) h.stableProjection (fun z ↦ negativeGradientRemainder f x (x + z)) r
    hs hu hN hsmall h.negativeGradientRemainder_centered_zero
    h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  refine ⟨r, hr, rho, hrho, ⟨(Homeomorph.setCongr ?_).trans (e.symm.trans ?_)⟩⟩
  · simp only [localStableSet, localInvariantSet]
    rw [← neg_gradient_centered_time_eq (f := f) (x := x)]
  · have hk : Module.finrank ℝ h.contDiffAt.stableLinearSubspace =
        Module.finrank ℝ E - morseIndex f x := by
      have := h.finrank_stableLinearSubspace_add_morseIndex
      omega
    have hrange : Set.range (h.stableProjection : E → E) =
        (h.contDiffAt.stableLinearSubspace : Set E) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_stableProjection
    exact euclideanClosedBallHomeomorph hrange hk rho

/-- **The local unstable set at a Morse critical point is a closed disk whose dimension is the
Morse index.** For suitable radii `r` and `rho`, the initial displacements of backward
negative-gradient solutions confined to `closedBall 0 r` and restricted by
`norm (unstableProjection z) ≤ rho` are homeomorphic to a closed ball of that dimension. -/
theorem exists_localUnstableSet_homeomorph_closedBall (h : IsNondegenerateCriticalPoint f x) :
    ∃ r > 0, ∃ rho > 0, Nonempty (h.localUnstableSet r rho ≃ₜ
      closedBall (0 : EuclideanSpace ℝ (Fin (morseIndex f x))) rho) := by
  obtain ⟨K, alpha, epsilon, r, hr, hs, hu, hN, hsmall, -⟩ := h.exists_lyapunovPerronData 1 one_pos
  obtain ⟨rho, hrho, ⟨e⟩⟩ := ContinuousLinearMap.exists_localUnstableSetHomeomorph
    (-hessianOperator f x) h.stableProjection (fun z ↦ negativeGradientRemainder f x (x + z)) r
    hs hu hN hsmall h.negativeGradientRemainder_centered_zero
    h.isIdempotentElem_stableProjection h.commute_neg_hessianOperator_stableProjection hr
  refine ⟨r, hr, rho, hrho, ⟨(Homeomorph.setCongr ?_).trans (e.symm.trans ?_)⟩⟩
  · simp only [localUnstableSet, localInvariantSet]
    rw [← neg_gradient_centered_time_eq (f := f) (x := x), ← h.unstableProjection_def]
  · have hrange : Set.range (ContinuousLinearMap.id ℝ E - h.stableProjection) =
        (h.contDiffAt.unstableLinearSubspace : Set E) := by
      rw [← h.unstableProjection_def]
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg (fun s : Submodule ℝ E ↦ (s : Set E)) h.range_unstableProjection
    exact euclideanClosedBallHomeomorph hrange h.contDiffAt.finrank_unstableLinearSubspace rho

/-- The zero displacement, which represents the critical point `x` in centred coordinates, lies
in the local stable set of any nonnegative radii: the constant displacement trajectory `y = 0`
solves the centred negative-gradient equation and stays in every ball of nonnegative radius. -/
theorem zero_mem_localStableSet (h : IsNondegenerateCriticalPoint f x) {r rho : ℝ}
    (hr : 0 ≤ r) (hrho : 0 ≤ rho) : (0 : E) ∈ h.localStableSet r rho :=
  zero_mem_localInvariantSet h.gradient_eq_zero _ _ hr hrho

/-- The zero displacement, which represents the critical point `x` in centred coordinates, lies
in the local unstable set of any nonnegative radii. -/
theorem zero_mem_localUnstableSet (h : IsNondegenerateCriticalPoint f x) {r rho : ℝ}
    (hr : 0 ≤ r) (hrho : 0 ≤ rho) : (0 : E) ∈ h.localUnstableSet r rho :=
  zero_mem_localInvariantSet h.gradient_eq_zero _ _ hr hrho

/-- **At a local minimum the local unstable set degenerates to a point.** A nondegenerate
critical point of Morse index `0` has no unstable directions, so for suitable radii the zero
displacement is the only admissible initial displacement of a backward negative-gradient
solution confined near `x`. -/
theorem exists_localUnstableSet_eq_singleton_of_morseIndex_eq_zero
    (h : IsNondegenerateCriticalPoint f x) (hind : morseIndex f x = 0) :
    ∃ r > 0, ∃ rho > 0, h.localUnstableSet r rho = {0} := by
  obtain ⟨r, hr, rho, hrho, ⟨e⟩⟩ := h.exists_localUnstableSet_homeomorph_closedBall
  have : Subsingleton (EuclideanSpace ℝ (Fin (morseIndex f x))) := by
    rw [hind]; infer_instance
  exact ⟨r, hr, rho, hrho,
    ((Set.subsingleton_coe _).1 e.toEquiv.subsingleton).eq_singleton_of_mem
      (h.zero_mem_localUnstableSet hr.le hrho.le)⟩

/-- **At a local maximum the local stable set degenerates to a point.** A nondegenerate critical
point whose Morse index is the dimension of the ambient space has no stable directions, so for
suitable radii the zero displacement is the only admissible initial displacement of a forward
negative-gradient solution confined near `x`. -/
theorem exists_localStableSet_eq_singleton_of_morseIndex_eq_finrank
    (h : IsNondegenerateCriticalPoint f x) (hind : morseIndex f x = Module.finrank ℝ E) :
    ∃ r > 0, ∃ rho > 0, h.localStableSet r rho = {0} := by
  obtain ⟨r, hr, rho, hrho, ⟨e⟩⟩ := h.exists_localStableSet_homeomorph_closedBall
  have : Subsingleton (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - morseIndex f x))) := by
    rw [hind, Nat.sub_self]; infer_instance
  exact ⟨r, hr, rho, hrho,
    ((Set.subsingleton_coe _).1 e.toEquiv.subsingleton).eq_singleton_of_mem
      (h.zero_mem_localStableSet hr.le hrho.le)⟩

end IsNondegenerateCriticalPoint

end TauCeti

end
