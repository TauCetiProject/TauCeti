/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal

/-!
# Length of radial geodesic segments

In a normal domain, the radial exponential curve from parameter `0` to `1` has length equal to the
norm of its initial velocity. This formula gives the length of the radial candidate path in a
normal neighbourhood.

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

/-- In a normal domain, the radial exponential curve from `0` to `1` has length `‖v‖`. -/
theorem pathELength_riemannianExp_smul_zero_one {p : M} {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) {v : TangentSpace I p} (hv : v ∈ U) :
    pathELength I (fun u : ℝ ↦ riemannianExp I M p (u • v)) 0 1 = ‖v‖ₑ := by
  have hcurve : (fun u : ℝ ↦ riemannianExp I M p (u • v)) = maximalGeodesic I M p v := by
    funext u
    exact riemannianExp_smul p v u
  rw [hcurve, pathELength_maximalGeodesic
    (h.mem_geodesicInterval hv (by norm_num) (by norm_num))
    (h.mem_geodesicInterval hv (by norm_num) (by norm_num)), sub_zero, ENNReal.ofReal_one,
    mul_one]

end TauCeti.Manifold

end
