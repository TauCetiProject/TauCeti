/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
import TauCeti.Topology.ContinuousOn.Extension
import TauCeti.Topology.Covering.Convex

/-!
# Completeness lifts along Riemannian coverings

Let `f : M → N` be a local Riemannian isometry from a boundaryless Riemannian manifold which is
moreover a topological covering map. If the geodesics of `N` leaving `f x` are defined for all
time, then so are the geodesics of `M` leaving `x`. Indeed, let `v ∈ T_x M` and let `γ` be the
all-time geodesic of `N` with initial data `(f x, df_x v)`. Since `ℝ` is simply connected and
locally path connected, `γ` lifts uniquely through the covering `f` to a continuous curve `Γ`
with `Γ 0 = x`. Since `f` is a local diffeomorphism (inverse function theorem), `Γ` is `C²`,
and since `f` is a local isometry, `Γ` is a geodesic. Its initial velocity is sent by the
injective differential `df_x` to `df_x v`, so it is `v`.

Consequently, by the Hopf–Rinow theorem, if `N` is complete for its Riemannian distance then so
is `M`, for any distance on `M` that is its Riemannian distance. For a preconnected Hausdorff `M`
this applies to the distance `TauCeti.MetricSpace.ofRiemannianMetric`, whose topology is the
manifold topology. No completeness assumption is made on `M`. The main application is to a
pullback metric `f^* g` along a smooth covering map with invertible differential.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.exists_isGeodesicCurveOnFrom_of_isCoveringMap`: geodesics
  on intervals lift with prescribed initial data; the all-time case is a corollary.
* `TauCeti.IsLocalRiemannianIsometry.geodesicInterval_mfderiv_of_isCoveringMap`: corresponding
  initial data have the same maximal geodesic interval.
* `TauCeti.IsLocalRiemannianIsometry.isGeodesicallyCompleteAt_of_isCoveringMap`: geodesic
  completeness at `f x` lifts to geodesic completeness at `x`.
* `TauCeti.IsLocalRiemannianIsometry.completeSpace_of_isCoveringMap`: metric completeness of `N`
  lifts to metric completeness of `M`.
* `Bundle.ContMDiffRiemannianMetric.isGeodesicallyCompleteAt_pullback_of_isCoveringMap`: the
  pullback of a geodesically complete metric along a smooth covering is geodesically complete.
* `Bundle.ContMDiffRiemannianMetric.completeSpace_pullback_of_isCoveringMap`: on a preconnected
  cover, the Riemannian distance of the pullback of a geodesically complete metric is complete.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 (complete manifolds).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6
  (completeness and Riemannian coverings).
-/

public section

open Bundle Manifold Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}

section Geodesic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [BoundarylessManifold I M] {f : M → N}

/-- A geodesic on an interval lifts through a Riemannian covering with prescribed initial data.
The lifted curve agrees with the base curve after projection throughout the parameter set. -/
theorem exists_isGeodesicCurveOnFrom_of_isCoveringMap
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f) {x : M}
    {v : TangentSpace I x} {γ : ℝ → N} {s : Set ℝ} (hs : s.OrdConnected)
    (hγ : IsGeodesicCurveOnFrom J γ s (f x) (mfderiv I J f x v)) :
    ∃ Γ : ℝ → M, IsGeodesicCurveOnFrom I Γ s x v ∧ EqOn (f ∘ Γ) γ s := by
  obtain ⟨L, ⟨hL0, hL⟩, -⟩ := hcov.existsUnique_continuousMap_lifts_of_convex hs.convex
    ⟨s.domRestrict γ, hγ.isGeodesicCurveOn.continuousOn.domRestrict⟩
    ⟨0, hγ.zero_mem⟩ x hγ.base_eq.symm
  have : Nonempty M := ⟨x⟩
  obtain ⟨Γ, hΓc, hΓL⟩ := L.continuous.exists_continuousOn_eq (A := s)
  have hΓ0 : Γ 0 = x := (hΓL ⟨0, hγ.zero_mem⟩).trans hL0
  have hΓγ : EqOn (f ∘ Γ) γ s := by
    intro t ht
    simpa only [Function.comp_apply, hΓL ⟨t, ht⟩, ContinuousMap.coe_mk, Set.domRestrict] using
      congrFun hL ⟨t, ht⟩
  have hΓ2 : ContMDiffOn 𝓘(ℝ) I 2 Γ s :=
    ContMDiffOn.of_comp_isLocalDiffeomorph
      (hf.isLocalDiffeomorph (n := 2) (by norm_num) (by simp)) hΓc
      (hγ.isGeodesicCurveOn.contMDiffOn.congr hΓγ)
  exact ⟨Γ, (hf.isGeodesicCurveOnFrom_comp_iff hΓ2 hΓ0).mp (hγ.congr hΓγ), hΓγ⟩

/-- An all-time geodesic lifts through a Riemannian covering with prescribed initial data. -/
theorem exists_isGeodesicCurveOnFrom_univ_of_isCoveringMap
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f) {x : M}
    {v : TangentSpace I x} {γ : ℝ → N}
    (hγ : IsGeodesicCurveOnFrom J γ univ (f x) (mfderiv I J f x v)) :
    ∃ Γ : ℝ → M, IsGeodesicCurveOnFrom I Γ univ x v ∧ f ∘ Γ = γ := by
  obtain ⟨Γ, hΓ, hΓγ⟩ := hf.exists_isGeodesicCurveOnFrom_of_isCoveringMap
    hcov ordConnected_univ hγ
  exact ⟨Γ, hΓ, funext fun t ↦ hΓγ (mem_univ t)⟩

end Geodesic

section GeodesicCompleteness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  [BoundarylessManifold I M] {f : M → N}

/-- A Riemannian covering preserves the maximal interval for corresponding initial data. -/
theorem geodesicInterval_mfderiv_of_isCoveringMap
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f) (x : M)
    (v : TangentSpace I x) :
    geodesicInterval J N (f x) (mfderiv I J f x v) = geodesicInterval I M x v := by
  refine Subset.antisymm ?_ (hf.geodesicInterval_subset_geodesicInterval_mfderiv x v)
  intro t ht
  rcases mem_geodesicInterval_iff.mp ht with ⟨γ, a, b, hγ, ht⟩
  obtain ⟨Γ, hΓ, -⟩ := hf.exists_isGeodesicCurveOnFrom_of_isCoveringMap
    hcov ordConnected_Ioo hγ
  exact mem_geodesicInterval_iff.mpr ⟨Γ, a, b, hΓ, ht⟩

/-- **Geodesic completeness lifts along a Riemannian covering.** If every geodesic leaving
`f x` is defined for all time, then every geodesic leaving `x` is defined for all time. -/
theorem isGeodesicallyCompleteAt_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) {x : M} (h : IsGeodesicallyCompleteAt J N (f x)) :
    IsGeodesicallyCompleteAt I M x := by
  refine isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval.2 fun v ↦ ?_
  rw [← hf.geodesicInterval_mfderiv_of_isCoveringMap hcov, h.geodesicInterval_eq_univ]
  exact mem_univ 1

/-- Geodesic completeness at corresponding points is equivalent along a Riemannian covering. -/
theorem isGeodesicallyCompleteAt_iff_of_isCoveringMap
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f) (x : M) :
    IsGeodesicallyCompleteAt J N (f x) ↔ IsGeodesicallyCompleteAt I M x :=
  ⟨hf.isGeodesicallyCompleteAt_of_isCoveringMap hcov, hf.isGeodesicallyCompleteAt⟩

/-- **Geodesic completeness lifts along a Riemannian covering**, global form. -/
theorem forall_isGeodesicallyCompleteAt_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) (h : ∀ y : N, IsGeodesicallyCompleteAt J N y) (x : M) :
    IsGeodesicallyCompleteAt I M x :=
  hf.isGeodesicallyCompleteAt_of_isCoveringMap hcov (h (f x))

end GeodesicCompleteness

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {N : Type*} [EMetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]
  [I.Boundaryless] [J.Boundaryless] {f : M → N}

/-- **Completeness lifts along a Riemannian covering.** If `f : M → N` is a local Riemannian
isometry between boundaryless Riemannian manifolds, whose distances are their Riemannian
distances, and a covering map, and `N` is complete, then `M` is complete. -/
theorem completeSpace_of_isCoveringMap [CompleteSpace N] (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) : CompleteSpace M := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · infer_instance
  · exact (completeSpace_iff_isGeodesicallyCompleteAt x).2
      (hf.isGeodesicallyCompleteAt_of_isCoveringMap hcov
        (isGeodesicallyCompleteAt_of_completeSpace (f x)))

end Metric

end TauCeti.IsLocalRiemannianIsometry

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **Pullback metrics along coverings are geodesically complete.** Let `f : M → N` be a smooth
covering map whose differential is everywhere invertible, and `g` a smooth Riemannian metric on
`N`. If every geodesic of `g` leaving `f x` is defined for all time, then so is every geodesic of
the pullback metric `f^* g` leaving `x`. -/
theorem isGeodesicallyCompleteAt_pullback_of_isCoveringMap [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (hcov : IsCoveringMap f) {x : M}
    (h : letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
      IsGeodesicallyCompleteAt J N (f x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
    IsGeodesicallyCompleteAt I M x :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  (isLocalRiemannianIsometry_pullback_of_isInvertible g hf hinv
    ).isGeodesicallyCompleteAt_of_isCoveringMap hcov h

/-- **Pullback metrics along coverings of complete manifolds are complete.** Let `f : M → N` be a
smooth covering map out of a preconnected Hausdorff manifold whose differential is everywhere
invertible, and `g` a smooth Riemannian metric on `N` all of whose geodesics are defined for all
time. Then `M` is complete for the Riemannian distance of the pullback metric `f^* g`. -/
theorem completeSpace_pullback_of_isCoveringMap [I.Boundaryless] [T2Space M] [PreconnectedSpace M]
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (hcov : IsCoveringMap f)
    (h : letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
      ∀ y : N, IsGeodesicallyCompleteAt J N y) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
    letI : MetricSpace M :=
      haveI := Manifold.locallyCompact_of_finiteDimensional (M := M) I
      haveI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
        (F := E) (V := fun x : M ↦ TangentSpace I x)
      MetricSpace.ofRiemannianMetric I M
    CompleteSpace M := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  have := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  let : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · infer_instance
  · exact (Manifold.completeSpace_iff_isGeodesicallyCompleteAt x).2
      (g.isGeodesicallyCompleteAt_pullback_of_isCoveringMap hf hinv hcov (h (f x)))

end Bundle.ContMDiffRiemannianMetric
