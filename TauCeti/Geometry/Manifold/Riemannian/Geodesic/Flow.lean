/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Trajectory

/-!
# The smooth geodesic flow

The geodesic spray of a smooth finite-dimensional Riemannian manifold has a family of integral
curves depending smoothly on the initial tangent vector and on time.  Projecting each spray
trajectory to the manifold gives the geodesic with that initial position and velocity, on one
common open time neighbourhood for all nearby initial data.

Globally, the maximal integral curves of the spray form the *geodesic flow* on the tangent bundle.
Its natural domain is the set of pairs `(z, t)` of a tangent vector `z ∈ T_x M` and a time `t` in
the maximal geodesic interval of `z`; this domain is open, the flow is jointly smooth on it, and so
is its base projection, the maximal geodesic regarded as a function of its initial data and time.
This is the smooth-dependence input for smoothness of the exponential map on its natural domain.

## Main results

* `TauCeti.Manifold.exists_contMDiffAt_localGeodesicFlow`: local spray trajectories form a
  jointly smooth family, and their base projections have the prescribed geodesic initial data.
* `TauCeti.Manifold.maximalIntegralCurveFlowDomain_geodesicSpray`: the domain of the
  geodesic flow consists of the pairs `(z, t)` with `t` in the maximal geodesic interval of `z`.
* `TauCeti.Manifold.isOpen_setOfPred_mem_geodesicInterval`: this domain is open in `TM × ℝ`.
* `TauCeti.Manifold.contMDiffOn_maximalIntegralCurve_geodesicSpray`: the maximal geodesic flow is
  smooth on its domain.
* `TauCeti.Manifold.contMDiffOn_maximalGeodesic`: maximal geodesics depend smoothly on their
  initial data and on time.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Chapter 5.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The smooth local geodesic flow.**  Near every initial state `z : TM`, the integral curves
of the geodesic spray exist on a common open time neighbourhood and depend smoothly on the initial
state and time at `(z, 0)`.  Their base projections are geodesics with the position and velocity
encoded by each nearby initial state.
-/
theorem exists_contMDiffAt_localGeodesicFlow (z : TangentBundle I M) :
    ∃ U ∈ nhds z, ∃ s ∈ nhds (0 : ℝ), IsOpen s ∧
      ∃ Φ : TangentBundle I M → ℝ → TangentBundle I M,
        CMDiffAt ∞ (fun p : TangentBundle I M × ℝ ↦ Φ p.1 p.2) (z, 0) ∧
          ∀ w ∈ U, Φ w 0 = w ∧
            IsMIntegralCurveOn (Φ w) (geodesicSpray I M) s ∧
            (∀ t ∈ s, ∀ u, Φ w (t + u) = Φ (Φ w t) u) ∧
            IsGeodesicCurveOnFrom I (fun t ↦ (Φ w t).proj) s w.proj w.2 := by
  obtain ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, hΦ⟩ :=
    exists_contMDiffAt_localFlow (I := I.tangent) (V := univ)
      (v := geodesicSpray I M) z contMDiff_infty_geodesicSpray.contMDiffOn univ_mem
  refine ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, ?_⟩
  intro w hw
  obtain ⟨hΦ0, hΦcurve, hΦadd⟩ := hΦ w hw
  refine ⟨hΦ0, hΦcurve, hΦadd, ?_⟩
  exact hΦcurve.isGeodesicCurveOnFrom_proj hsopen (mem_of_mem_nhds hs) hΦ0

/-! ### The maximal geodesic flow -/

/-- The domain of the maximal flow of the geodesic spray consists of the pairs `(z, t)` for which
`t` lies in the maximal geodesic interval of the initial data encoded by `z`. -/
theorem maximalIntegralCurveFlowDomain_geodesicSpray :
    maximalIntegralCurveFlowDomain (geodesicSpray I M) =
      {q : TangentBundle I M × ℝ | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  ext ⟨z, t⟩
  rw [mem_maximalIntegralCurveFlowDomain, mem_ofPred_eq,
    ← maximalIntegralCurveInterval_geodesicSpray]

variable [T2Space M]

/-- **The domain of the geodesic flow is open**: the pairs `(z, t)` of a tangent vector and a
time of its maximal geodesic interval form an open subset of `TM × ℝ`. -/
theorem isOpen_setOfPred_mem_geodesicInterval :
    IsOpen {q : TangentBundle I M × ℝ | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  rw [← maximalIntegralCurveFlowDomain_geodesicSpray]
  exact isOpen_maximalIntegralCurveFlowDomain contMDiff_one_geodesicSpray

/-- **The maximal geodesic flow is smooth.**  The maximal integral curves of the geodesic spray
depend smoothly, jointly in the initial tangent vector and in time, on the domain of the
geodesic flow. -/
theorem contMDiffOn_maximalIntegralCurve_geodesicSpray :
    ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I.tangent ∞
      (fun q : TangentBundle I M × ℝ ↦ maximalIntegralCurve (geodesicSpray I M) q.1 q.2)
      {q | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} := by
  rw [← maximalIntegralCurveFlowDomain_geodesicSpray]
  exact contMDiffOn_maximalIntegralCurve (I := I.tangent) (n := (⊤ : ℕ∞)) (by simp)
    contMDiff_infty_geodesicSpray

/-- **Smooth dependence of maximal geodesics on initial data.**  The maximal geodesic with initial
point `z.proj` and initial velocity `z.2`, evaluated at time `t`, is a smooth function of
`(z, t)` on the domain of the geodesic flow. -/
theorem contMDiffOn_maximalGeodesic :
    ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : TangentBundle I M × ℝ ↦ maximalGeodesic I M q.1.proj q.1.2 q.2)
      {q | q.2 ∈ geodesicInterval I M q.1.proj q.1.2} :=
  ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x) (n := ∞)).comp_contMDiffOn
    contMDiffOn_maximalIntegralCurve_geodesicSpray).congr fun _ _ ↦ maximalGeodesic_def _ _ _

end TauCeti.Manifold

end
