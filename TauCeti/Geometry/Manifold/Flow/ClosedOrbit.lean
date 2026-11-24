/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow

/-!
# Circle parametrizations of periodic trajectories on manifolds

Let `ϕ` be a continuous flow by `ℝ` on a manifold `M`, and let `c : Flow.PeriodicTrajectory ϕ` be a
periodic trajectory of period `c.period`. Because the quotient map `ℝ → AddCircle c.period` is a
surjective local diffeomorphism (`AddCircle.isLocalDiffeomorph_coe`), the circle parametrization
`c.circleMap : AddCircle c.period → M` has the same `C^n` regularity as its real lift
`s ↦ ϕ s c.point`, and when that lift is an integral curve of a vector field `v` its velocity at
each `θ : AddCircle c.period` is `v (c.circleMap θ)`. Specializing to the global flow of a complete
vector field yields `C^n` regularity and velocity equal to the vector field along periodic
trajectories of `TauCeti.globalFlow`.

## Main results

* `Flow.PeriodicTrajectory.contMDiff_circleMap_iff`: `c.circleMap` is `C^n` (`n : ℕ∞ω`) if and only
  if `s ↦ ϕ s c.point` is `C^n`.
* `Flow.PeriodicTrajectory.hasMFDerivAt_circleMap`: when `s ↦ ϕ s c.point` is an integral curve of
  `v`, `c.circleMap` has manifold derivative `r ↦ r • v (c.circleMap θ)` at every `θ`.
* `TauCeti.contMDiff_circleMap_globalFlow`, `TauCeti.hasMFDerivAt_circleMap_globalFlow`:
  specialization to periodic trajectories of `TauCeti.globalFlow`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Chapter 9.
-/

public section

open scoped ContDiff Manifold

namespace Flow.PeriodicTrajectory

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {ϕ : Flow ℝ M}

/-- The circle parametrization `c.circleMap` of a periodic trajectory is `C^n` (`n : ℕ∞ω`) if and
only if its real lift `s ↦ ϕ s c.point` is `C^n`. -/
theorem contMDiff_circleMap_iff (c : Flow.PeriodicTrajectory ϕ) {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ) I n c.circleMap ↔ ContMDiff 𝓘(ℝ) I n (fun s ↦ ϕ s c.point) := by
  have hcomp : c.circleMap ∘ ((↑) : ℝ → AddCircle c.period) = fun s ↦ ϕ s c.point :=
    funext c.circleMap_coe
  rw [← (AddCircle.isLocalDiffeomorph_coe c.period n).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl, hcomp]

/-- If `s ↦ ϕ s c.point` is an integral curve of `v`, then `c.circleMap` is differentiable at `θ`
with velocity `v (c.circleMap θ)`. -/
theorem hasMFDerivAt_circleMap (c : Flow.PeriodicTrajectory ϕ)
    {v : (x : M) → TangentSpace I x} (h : IsMIntegralCurve (fun s ↦ ϕ s c.point) v)
    (θ : AddCircle c.period) :
    HasMFDerivAt 𝓘(ℝ) I c.circleMap θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (c.circleMap θ))) := by
  induction θ using QuotientAddGroup.induction_on with
  | H t =>
    have hcomp : c.circleMap ∘ ((↑) : ℝ → AddCircle c.period) =
        fun s ↦ ϕ s c.point := funext c.circleMap_coe
    have hlift : HasMFDerivAt 𝓘(ℝ) I (c.circleMap ∘ ((↑) : ℝ → AddCircle c.period)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (c.circleMap t))) := by
      rw [hcomp, c.circleMap_coe]
      exact h t
    have hd : MDifferentiableAt 𝓘(ℝ) I c.circleMap t :=
      ((AddCircle.isLocalDiffeomorph_coe c.period 1 t).mdifferentiableAt_comp_iff one_ne_zero).1
        hlift.mdifferentiableAt
    rw [← AddCircle.mfderiv_comp_coe.symm.trans hlift.mfderiv]
    exact hd.hasMFDerivAt

end Flow.PeriodicTrajectory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]
  [BoundarylessManifold I M]
  {v : (x : M) → TangentSpace I x}
  (hv : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
  (hcomplete : IsCompleteVectorField v)

/-- For a complete `C^n` vector field (`1 ≤ n`), the circle parametrization `c.circleMap` of any
periodic trajectory of `globalFlow` is `C^n`. -/
theorem contMDiff_circleMap_globalFlow {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    (hvn : ContMDiff I I.tangent n (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (c : Flow.PeriodicTrajectory
      (globalFlow v (hvn.of_le (by exact_mod_cast hn)) hcomplete)) :
    ContMDiff 𝓘(ℝ) I n c.circleMap :=
  c.contMDiff_circleMap_iff.2 <|
    (contMDiff_globalFlow_uncurry hcomplete hn hvn).comp (contMDiff_id.prodMk contMDiff_const)

include hv hcomplete in
/-- For a complete `C¹` vector field `v`, the circle parametrization `c.circleMap` of any periodic
trajectory of `globalFlow` is differentiable at `θ` with velocity `v (c.circleMap θ)`. -/
theorem hasMFDerivAt_circleMap_globalFlow
    (c : Flow.PeriodicTrajectory (globalFlow v hv hcomplete)) (θ : AddCircle c.period) :
    HasMFDerivAt 𝓘(ℝ) I c.circleMap θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (c.circleMap θ))) :=
  c.hasMFDerivAt_circleMap (isMIntegralCurve_globalFlow hv hcomplete c.point) θ

end TauCeti
