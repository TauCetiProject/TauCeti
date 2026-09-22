/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal

/-!
# Length of radial geodesic segments

The radial curve is a reparametrized maximal geodesic wherever its parameters lie in the interval
of existence.  These results record its Riemannian length directly in exponential-map coordinates,
so it can be compared with the length of a competing path in a normal neighbourhood.

The length calculation uses the constant-speed formula for maximal geodesics in
`TauCeti.Manifold.pathELength_maximalGeodesic`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

/-- A radial segment has length equal to its constant speed times the elapsed time whenever both
parameters lie in the interval of existence. -/
theorem pathELength_radialSegment {p : M} {v : TangentSpace I p} {s t : ℝ}
    (hs : s ∈ geodesicInterval I M p v) (ht : t ∈ geodesicInterval I M p v) :
    pathELength I (fun u : ℝ ↦ riemannianExp I M p (u • v)) s t =
      ‖v‖ₑ * ENNReal.ofReal (t - s) := by
  have hcurve : (fun u : ℝ ↦ riemannianExp I M p (u • v)) = maximalGeodesic I M p v := by
    funext u
    exact riemannianExp_smul p v u
  rw [hcurve]
  exact pathELength_maximalGeodesic hs ht

/-- In particular, when `exp_p v` is defined, the radial segment from `p` to `exp_p v` has length
equal to `‖v‖`. -/
theorem pathELength_radialSegment_zero_one {p : M} {v : TangentSpace I p}
    (hv : v ∈ expDomain I M p) :
    pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 = ‖v‖ₑ := by
  have hIcc : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.mp hv)
  rw [pathELength_radialSegment (hIcc (by simp)) (hIcc (by simp))]
  simp

end TauCeti.Manifold

end
