/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed

/-!
# Local injectivity of geodesics

A geodesic with nonzero velocity is injective near every interior parameter in the same
connected component, since its derivative is injective there. This local property is used
to extract simple geodesic arcs from radial geodesics.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.exists_mem_nhds_injOn`: a geodesic with nonzero velocity
  is locally injective at interior parameters in the same connected component.
* `TauCeti.Manifold.exists_mem_nhds_injOn_maximalGeodesic`: a maximal geodesic with nonzero
  initial velocity is locally injective on its maximal interval.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 5 and 6.
-/

public section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

section LocalInjectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- A geodesic with nonzero velocity at `a` is locally injective at every interior parameter in
its connected component. -/
theorem IsGeodesicCurveOn.exists_mem_nhds_injOn {γ : ℝ → M} {s : Set ℝ}
    (h : IsGeodesicCurveOn I γ s) {a t : ℝ} (ht : t ∈ connectedComponentIn s a)
    (hs : s ∈ 𝓝 t) (ha : curveVelocityWithin I γ s a ≠ 0) :
    ∃ U ∈ 𝓝 t, InjOn γ U := by
  apply (h.contMDiffOn.contMDiffAt hs).exists_mem_nhds_injOn_of_curveVelocity_ne_zero (by simp)
  rw [← curveVelocityWithin_of_mem_nhds hs]
  exact h.curveVelocityWithin_ne_zero_of_mem_connectedComponentIn ht ha

end LocalInjectivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p}

/-- **Geodesics are locally injective.** A maximal geodesic with nonzero initial velocity is
injective on a neighbourhood of each parameter of its maximal interval. -/
theorem exists_mem_nhds_injOn_maximalGeodesic {t : ℝ} (hv : v ≠ 0)
    (ht : t ∈ geodesicInterval I M p v) :
    ∃ U ∈ 𝓝 t, InjOn (maximalGeodesic I M p v) U := by
  exact (isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.exists_mem_nhds_injOn
    (mem_connectedComponentIn ht) (isOpen_geodesicInterval.mem_nhds ht)
    (by simpa only [curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds ht)] using
      curveVelocity_maximalGeodesic_ne_zero hv ht)

end TauCeti.Manifold
