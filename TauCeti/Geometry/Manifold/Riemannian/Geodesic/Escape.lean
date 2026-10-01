/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Topology.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# The escape lemma for geodesics

At a finite endpoint of its maximal interval, a maximal geodesic leaves every compact subset of the
manifold. A maximal geodesic travels at constant speed, so its velocity lift stays among the
tangent vectors of norm at most the initial speed. Over a compact subset of the manifold these
vectors form a compact subset of the tangent bundle, and an integral curve of the geodesic spray
cannot remain in a compact set as it approaches a finite endpoint of its maximal interval.

The step about velocities is not implicit in constant speed: that bounds the velocity in the
fibrewise Riemannian norm, and it is the compactness of the norm-bounded part of a Riemannian
bundle over a compact set which converts such a bound into relative compactness in the total
space.

The escape lemma shows that metric completeness implies geodesic completeness, and it computes
maximal geodesic intervals in examples: a geodesic that stays in a compact set up to a finite time
is still defined at that time.

## Main results

* `TauCeti.Manifold.eventually_notMem_nhdsLT_maximalGeodesic`: the escape lemma at a finite right
  endpoint of the maximal interval.
* `TauCeti.Manifold.eventually_notMem_nhdsGT_maximalGeodesic`: the escape lemma at a finite left
  endpoint.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Lemma 9.19 (the escape
  lemma for integral curves).
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6 (its use in the
  Hopf–Rinow theorem).
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space M] [T2Space (TangentBundle I M)]

variable {p : M} {v : TangentSpace I p}

omit [T2Space M] in
/-- Along its maximal interval, the velocity lift of a maximal geodesic lies over the geodesic and
has the norm of the initial velocity. -/
private theorem maximalIntegralCurve_geodesicSpray_mem_norm_le {K : Set M} {t : ℝ}
    (ht : t ∈ geodesicInterval I M p v) (hK : maximalGeodesic I M p v t ∈ K) :
    maximalIntegralCurve (geodesicSpray I M) (TotalSpace.mk' E p v) t ∈
      {z : TangentBundle I M | z.proj ∈ K ∧ ‖z.2‖ ≤ ‖v‖} := by
  have h := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  rw [maximalIntegralCurve_geodesicSpray ht]
  refine ⟨hK, le_of_eq ?_⟩
  rw [h.isGeodesicCurveOn.norm_curveVelocityWithin_eq isPreconnected_geodesicInterval ht
    zero_mem_geodesicInterval]
  exact congrArg (fun z : TangentBundle I M ↦ ‖z.2‖) h.initial_eq

/-- **The escape lemma for geodesics at a finite right endpoint.** If the maximal interval of the
geodesic with initial data `(p, v)` is bounded above, with least upper bound `b`, the maximal
geodesic leaves every compact set as `t → b⁻`. -/
theorem eventually_notMem_nhdsLT_maximalGeodesic {b : ℝ}
    (hb : IsLUB (geodesicInterval I M p v) b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, maximalGeodesic I M p v t ∉ K := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isLUB hb
  rw [← maximalIntegralCurveInterval_geodesicSpray] at hb
  filter_upwards [eventually_notMem_nhdsLT_maximalIntegralCurve contMDiff_one_geodesicSpray
    ((maximalIntegralCurveInterval_geodesicSpray p v).symm ▸ zero_mem_geodesicInterval) hb
    (hK.norm_le_bundle ‖v‖), Ioo_mem_nhdsLT (ha.trans hb0)] with t hnot ht hmem
  exact hnot (maximalIntegralCurve_geodesicSpray_mem_norm_le (hsub ht) hmem)

/-- **The escape lemma for geodesics at a finite left endpoint.** If the maximal interval of the
geodesic with initial data `(p, v)` is bounded below, with greatest lower bound `a`, the maximal
geodesic leaves every compact set as `t → a⁺`. -/
theorem eventually_notMem_nhdsGT_maximalGeodesic {a : ℝ}
    (ha : IsGLB (geodesicInterval I M p v) a) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[>] a, maximalGeodesic I M p v t ∉ K := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_geodesicInterval_of_isGLB ha
  rw [← maximalIntegralCurveInterval_geodesicSpray] at ha
  filter_upwards [eventually_notMem_nhdsGT_maximalIntegralCurve contMDiff_one_geodesicSpray
    ((maximalIntegralCurveInterval_geodesicSpray p v).symm ▸ zero_mem_geodesicInterval) ha
    (hK.norm_le_bundle ‖v‖), Ioo_mem_nhdsGT (ha0.trans hb)] with t hnot ht hmem
  exact hnot (maximalIntegralCurve_geodesicSpray_mem_norm_le (hsub ht) hmem)

end TauCeti.Manifold

end
