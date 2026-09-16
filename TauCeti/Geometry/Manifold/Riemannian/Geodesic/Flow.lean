/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.SmoothFlow
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness

/-!
# The smooth local geodesic flow

The geodesic spray of a smooth finite-dimensional Riemannian manifold has a family of integral
curves depending smoothly on the initial tangent vector and on time.  Projecting each spray
trajectory to the manifold gives the geodesic with that initial position and velocity, on one
common open time neighbourhood for all nearby initial data.

The result here is local at an arbitrary state of the tangent bundle.  It is the smooth-dependence
input for the maximal geodesic flow and for smoothness of the exponential map on its natural
domain.

## Main result

* `TauCeti.Manifold.exists_contMDiffAt_localGeodesicFlow`: local spray trajectories form a
  jointly smooth family, and their base projections have the prescribed geodesic initial data.

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
  have hspray : CMDiff ∞ (fun w : TangentBundle I M ↦
      (⟨w, geodesicSpray I M w⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    contMDiff_geodesicSpray (I := I) (M := M) (n := ∞) (m := ∞) (k := ∞)
      (by simp) (by simp)
  obtain ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, hΦ⟩ :=
    exists_contMDiffAt_localFlow (I := I.tangent) (V := univ)
      (v := geodesicSpray I M) z hspray.contMDiffOn univ_mem
  refine ⟨U, hU, s, hs, hsopen, Φ, hΦsmooth, ?_⟩
  intro w hw
  obtain ⟨hΦ0, hΦcurve, hΦadd⟩ := hΦ w hw
  refine ⟨hΦ0, hΦcurve, hΦadd, ?_⟩
  exact hΦcurve.isGeodesicCurveOnFrom_proj hsopen (mem_of_mem_nhds hs) hΦ0

end TauCeti.Manifold

end
