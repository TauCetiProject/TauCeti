/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.PathELength

/-!
# Length of maximal geodesics

A maximal geodesic has constant speed on its maximal interval, so its Riemannian length between
any two parameters in that interval is its initial speed times the elapsed time. This gives the
Lipschitz bound used in the metric-completeness argument for geodesic completeness.

## Main results

* `TauCeti.Manifold.norm_curveVelocityWithin_maximalGeodesic`: the velocity of a maximal geodesic
  has the norm of its initial velocity throughout its interval.
* `TauCeti.Manifold.pathELength_maximalGeodesic`: its length between two parameters is its initial
  speed times the elapsed time.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Manifold MeasureTheory Set
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

variable {p : M} {v : TangentSpace I p}

/-- At every parameter of its maximal interval, the maximal geodesic from `p` with initial
velocity `v` has velocity of norm `‖v‖`. -/
theorem norm_curveVelocityWithin_maximalGeodesic {t : ℝ} (ht : t ∈ geodesicInterval I M p v) :
    ‖curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) t‖ = ‖v‖ := by
  have h := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  rw [h.isGeodesicCurveOn.norm_curveVelocityWithin_eq isPreconnected_geodesicInterval ht
    zero_mem_geodesicInterval]
  exact congrArg (fun z : TangentBundle I M ↦ ‖z.2‖) h.initial_eq

/-- Between two parameters of its maximal interval, the maximal geodesic from `p` with initial
velocity `v` has length `‖v‖ * (t - s)`. -/
theorem pathELength_maximalGeodesic {s t : ℝ} (hs : s ∈ geodesicInterval I M p v)
    (ht : t ∈ geodesicInterval I M p v) :
    pathELength I (maximalGeodesic I M p v) s t = ‖v‖ₑ * ENNReal.ofReal (t - s) := by
  have hsub : Ioo s t ⊆ geodesicInterval I M p v :=
    Ioo_subset_Icc_self.trans (ordConnected_geodesicInterval.out hs ht)
  have key : ∀ u ∈ Ioo s t,
      ‖mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic I M p v) u 1‖ₑ = ‖v‖ₑ := by
    intro u hu
    have hmem := hsub hu
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (maximalGeodesic I M p v) u 1 =
        curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) u :=
      ((curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds hmem)).trans
        (curveVelocity_apply (I := I))).symm
    rw [hvel, ← ofReal_norm, ← ofReal_norm, norm_curveVelocityWithin_maximalGeodesic hmem]
  rw [pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun measurableSet_Ioo key,
    setLIntegral_const, Real.volume_Ioo]

end TauCeti.Manifold

end
