/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal

/-!
# Length of radial geodesic segments

The radial curve is a reparametrized maximal geodesic wherever its parameters lie in the interval
of existence. Its directed length from parameter `s` to `t` is its speed times
`ENNReal.ofReal (t - s)`, so it is zero when `t < s`. These results record this length directly in
exponential-map coordinates, so it can be compared with the length of a competing path in a normal
neighbourhood.

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

/-- The directed length from `s` to `t` of the radial exponential curve equals its constant speed
times `ENNReal.ofReal (t - s)` whenever both parameters lie in the interval of existence. In
particular, it is zero when `t < s`. -/
theorem pathELength_riemannianExp_smul {p : M} {v : TangentSpace I p} {s t : ℝ}
    (hs : s ∈ geodesicInterval I M p v) (ht : t ∈ geodesicInterval I M p v) :
    pathELength I (fun u : ℝ ↦ riemannianExp I M p (u • v)) s t =
      ‖v‖ₑ * ENNReal.ofReal (t - s) := by
  have hcurve : (fun u : ℝ ↦ riemannianExp I M p (u • v)) = maximalGeodesic I M p v := by
    funext u
    exact riemannianExp_smul p v u
  rw [hcurve]
  exact pathELength_maximalGeodesic hs ht

/-- In a normal domain, the radial exponential curve from `0` to `1` has length `‖v‖`. -/
@[simp] theorem pathELength_riemannianExp_smul_zero_one {p : M} {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) {v : TangentSpace I p} (hv : v ∈ U) :
    pathELength I (fun u : ℝ ↦ riemannianExp I M p (u • v)) 0 1 = ‖v‖ₑ := by
  rw [pathELength_riemannianExp_smul
    (h.mem_geodesicInterval hv (by norm_num) (by norm_num))
    (h.mem_geodesicInterval hv (by norm_num) (by norm_num)), sub_zero, ENNReal.ofReal_one,
    mul_one]

end TauCeti.Manifold

end
