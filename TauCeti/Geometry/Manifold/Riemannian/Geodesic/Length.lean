/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
public import TauCeti.Geometry.Manifold.Riemannian.PathELength

/-!
# Length of geodesics

A geodesic has constant speed on a preconnected parameter set, so its directed Riemannian length
from parameter `s` to `t` is its speed times `ENNReal.ofReal (t - s)`; the length is zero when
`t < s`. For maximal geodesics this gives the Lipschitz bound used in the metric-completeness
argument for geodesic completeness.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.pathELength_eq`: on a preconnected parameter set, the
  directed length of a geodesic is its speed times the elapsed time.
* `TauCeti.Manifold.norm_curveVelocityWithin_maximalGeodesic`: the velocity of a maximal geodesic
  has the norm of its initial velocity throughout its interval.
* `TauCeti.Manifold.pathELength_maximalGeodesic`: its directed length from `s` to `t` is its
  initial speed times `ENNReal.ofReal (t - s)`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

section ConstantSpeed

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ}

/-- On an interval with endpoints in its preconnected domain, the directed length of a geodesic
from `a` to `b` is its speed at any chosen time in that domain times `ENNReal.ofReal (b - a)`. The
domain need not be open, so this applies to geodesic segments on closed intervals. -/
theorem IsGeodesicCurveOn.pathELength_eq (h : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b c : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    pathELength I γ a b = ‖curveVelocityWithin I γ s c‖ₑ * ENNReal.ofReal (b - a) := by
  have hsub : Icc a b ⊆ s := hconn.ordConnected.out ha hb
  have key : ∀ t ∈ Ioo a b,
      ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ = ‖curveVelocityWithin I γ s c‖ₑ := by
    intro t ht
    have hnhds : s ∈ 𝓝 t :=
      mem_nhds_iff.2 ⟨Ioo a b, Ioo_subset_Icc_self.trans hsub, isOpen_Ioo, ht⟩
    have hvel : mfderiv 𝓘(ℝ, ℝ) I γ t 1 = curveVelocityWithin I γ s t :=
      ((curveVelocityWithin_of_mem_nhds hnhds).trans (curveVelocity_apply (I := I))).symm
    rw [hvel, ← ofReal_norm, ← ofReal_norm,
      h.norm_curveVelocityWithin_eq hconn (hsub (Ioo_subset_Icc_self ht)) hc]
  rw [pathELength_eq_lintegral_mfderiv_Ioo, setLIntegral_congr_fun measurableSet_Ioo key,
    setLIntegral_const, Real.volume_Ioo]

end ConstantSpeed

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable {p : M} {v : TangentSpace I p}

/-- At every parameter of its maximal interval, the maximal geodesic from `p` with initial
velocity `v` has velocity of norm `‖v‖`. -/
theorem norm_curveVelocityWithin_maximalGeodesic {t : ℝ} (ht : t ∈ geodesicInterval I M p v) :
    ‖curveVelocityWithin I (maximalGeodesic I M p v) (geodesicInterval I M p v) t‖ = ‖v‖ := by
  have h := isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v
  rw [h.isGeodesicCurveOn.norm_curveVelocityWithin_eq isPreconnected_geodesicInterval ht
    zero_mem_geodesicInterval]
  exact congrArg (fun z : TangentBundle I M ↦ ‖z.2‖) h.initial_eq

/-- The directed length from `s` to `t` of the maximal geodesic from `p` with initial velocity `v`
is `‖v‖ * ENNReal.ofReal (t - s)`, and hence is zero when `t < s`. -/
theorem pathELength_maximalGeodesic {s t : ℝ} (hs : s ∈ geodesicInterval I M p v)
    (ht : t ∈ geodesicInterval I M p v) :
    pathELength I (maximalGeodesic I M p v) s t = ‖v‖ₑ * ENNReal.ofReal (t - s) := by
  rw [(isGeodesicCurveOnFrom_maximalGeodesic p v).isGeodesicCurveOn.pathELength_eq
    isPreconnected_geodesicInterval hs ht zero_mem_geodesicInterval, ← ofReal_norm, ← ofReal_norm,
    norm_curveVelocityWithin_maximalGeodesic zero_mem_geodesicInterval]

end TauCeti.Manifold

end
