/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.HopfRinow
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# Completeness lifts along Riemannian coverings

Let `f : M → N` be a local Riemannian isometry between boundaryless Riemannian manifolds which is
moreover a topological covering map. If the geodesics of `N` leaving `f x` are defined for all
time, then so are the geodesics of `M` leaving `x`. Indeed, let `v ∈ T_x M` and let `γ` be the
all-time geodesic of `N` with initial data `(f x, df_x v)`. Since `ℝ` is simply connected and
locally path connected, `γ` lifts uniquely through the covering `f` to a continuous curve `Γ`
with `Γ 0 = x`. Since `f` is a local diffeomorphism (inverse function theorem), `Γ` is smooth,
and since `f` is a local isometry, `Γ` is a geodesic. Its initial velocity is sent by the
injective differential `df_x` to `df_x v`, so it is `v`.

Consequently, by the Hopf–Rinow theorem, if `N` is complete for its Riemannian distance then so
is `M`, for any distance on `M` that is its Riemannian distance. For a connected Hausdorff `M`
this applies to the distance `TauCeti.MetricSpace.ofRiemannianMetric`, whose topology is the
manifold topology. No completeness assumption is made on `M`. The main application is to a
pullback metric `f^* g` along a smooth covering map with invertible differential.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.exists_isGeodesicCurveOnFrom_univ_of_isCoveringMap`: an
  all-time geodesic of `N` lifts to an all-time geodesic of `M` with prescribed initial point.
* `TauCeti.IsLocalRiemannianIsometry.isGeodesicallyCompleteAt_of_isCoveringMap`: geodesic
  completeness at `f x` lifts to geodesic completeness at `x`.
* `TauCeti.IsLocalRiemannianIsometry.completeSpace_of_isCoveringMap`: metric completeness of `N`
  lifts to metric completeness of `M`.
* `Bundle.ContMDiffRiemannianMetric.isGeodesicallyCompleteAt_pullback_of_isCoveringMap`: the
  pullback of a geodesically complete metric along a smooth covering is geodesically complete.
* `Bundle.ContMDiffRiemannianMetric.completeSpace_pullback_of_isCoveringMap`: on a connected
  cover, the Riemannian distance of the pullback of a geodesically complete metric is complete.
* `TauCeti.Manifold.t3Space`: a Hausdorff manifold with finite-dimensional model is regular, as
  needed to install its Riemannian distance.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 (complete manifolds).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 6
  (completeness and Riemannian coverings).
-/

public section

open Bundle Manifold Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- A Hausdorff manifold modelled on a finite-dimensional real space is regular, being locally
compact. -/
theorem t3Space (I : ModelWithCorners ℝ E H) : T3Space M :=
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  inferInstance

end TauCeti.Manifold

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}

section Geodesic

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

omit [FiniteDimensional ℝ F] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] in
/-- A local Riemannian isometry out of a boundaryless manifold is a local diffeomorphism of every
finite order `n ≥ 1`, by the inverse function theorem. -/
theorem isLocalDiffeomorph [BoundarylessManifold I M] (hf : IsLocalRiemannianIsometry I J f)
    {n : ℕ} (hn : 1 ≤ n) : IsLocalDiffeomorph I J n f :=
  TauCeti.isLocalDiffeomorph_of_mfderiv_eq (hf.contMDiff.of_le (by simp)) (by exact_mod_cast hn)
    hf.isInvertible_mfderiv

/-- **Lifting all-time geodesics through a Riemannian covering.** If `f : M → N` is a local
Riemannian isometry out of a boundaryless manifold and a covering map, every geodesic of `N`
defined for all time and leaving `f x` with velocity `df_x v` is the image of a geodesic of `M`
defined for all time and leaving `x` with velocity `v`. -/
theorem exists_isGeodesicCurveOnFrom_univ_of_isCoveringMap [BoundarylessManifold I M]
    (hf : IsLocalRiemannianIsometry I J f) (hcov : IsCoveringMap f) {x : M}
    {v : TangentSpace I x} {γ : ℝ → N}
    (hγ : IsGeodesicCurveOnFrom J γ univ (f x) (mfderiv I J f x v)) :
    ∃ Γ : ℝ → M, IsGeodesicCurveOnFrom I Γ univ x v ∧ f ∘ Γ = γ := by
  have hγc : Continuous γ := by
    rw [← continuousOn_univ]
    exact hγ.isGeodesicCurveOn.contMDiffOn.continuousOn
  have hγ0 : γ 0 = f x := by
    simpa using congrArg TotalSpace.proj hγ.initial_eq
  obtain ⟨Γ, ⟨hΓ0, hΓ⟩, -⟩ :=
    hcov.existsUnique_continuousMap_lifts ⟨γ, hγc⟩ 0 x hγ0.symm
  have hΓγ : f ∘ Γ = γ := hΓ
  have hΓ2 : ContMDiff 𝓘(ℝ) I 2 Γ := by
    refine ContMDiff.of_comp_isLocalDiffeomorph (hf.isLocalDiffeomorph (n := 2) (by norm_num))
      Γ.continuous ?_
    rw [hΓγ, ← contMDiffOn_univ]
    exact hγ.isGeodesicCurveOn.contMDiffOn
  have hgeod : IsGeodesicCurveOn I Γ univ := by
    rw [← hf.isGeodesicCurveOn_comp_iff hΓ2.contMDiffOn, hΓγ]
    exact hγ.isGeodesicCurveOn
  refine ⟨Γ, ⟨hgeod, mem_univ 0, ?_⟩, hΓγ⟩
  have hlift := tangentMap_curveVelocityLiftWithin (hf.mdifferentiableAt (Γ 0))
    (hgeod.mdifferentiableOn 0 (mem_univ 0))
    (hgeod.uniqueDiffOn 0 (mem_univ 0)).uniqueMDiffWithinAt
  rw [hΓγ, curveVelocityLiftWithin_apply, curveVelocityLiftWithin_apply, hγ.initial_eq] at hlift
  have key : ∀ (y : M) (w : TangentSpace I y), y = x →
      tangentMap I J f (TotalSpace.mk' E y w) =
        TotalSpace.mk' F (f x) (mfderiv I J f x v) →
      TotalSpace.mk' E y w = TotalSpace.mk' E x v := by
    rintro y w rfl h
    have h' : mfderiv I J f y w = mfderiv I J f y v := by
      simpa [tangentMap] using h
    rw [hf.mfderiv_injective y h']
  exact key _ _ hΓ0 hlift

variable [I.Boundaryless] [J.Boundaryless] [T2Space N]

/-- **Geodesic completeness lifts along a Riemannian covering.** If `f : M → N` is a local
Riemannian isometry between boundaryless manifolds and a covering map, and every geodesic of `N`
leaving `f x` is defined for all time, then every geodesic of `M` leaving `x` is defined for all
time. -/
theorem isGeodesicallyCompleteAt_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) {x : M} (h : IsGeodesicallyCompleteAt J N (f x)) :
    IsGeodesicallyCompleteAt I M x := by
  rw [isGeodesicallyCompleteAt_iff_forall_one_mem_geodesicInterval]
  intro v
  have hγ := isGeodesicCurveOnFrom_maximalGeodesic (I := J) (M := N) (f x) (mfderiv I J f x v)
  rw [geodesicInterval_eq_preimage_expDomain, expDomain_eq_univ_iff.2 h, preimage_univ] at hγ
  obtain ⟨Γ, hΓ, -⟩ := hf.exists_isGeodesicCurveOnFrom_univ_of_isCoveringMap hcov hγ
  exact mem_geodesicInterval_iff.2 ⟨Γ, -2, 2,
    hΓ.mono (uniqueDiffOn_Ioo _ _) (subset_univ _) ⟨by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-- **Geodesic completeness lifts along a Riemannian covering**, global form. -/
theorem forall_isGeodesicallyCompleteAt_of_isCoveringMap (hf : IsLocalRiemannianIsometry I J f)
    (hcov : IsCoveringMap f) (h : ∀ y : N, IsGeodesicallyCompleteAt J N y) (x : M) :
    IsGeodesicallyCompleteAt I M x :=
  hf.isGeodesicallyCompleteAt_of_isCoveringMap hcov (h (f x))

end Geodesic

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
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
  [I.Boundaryless] [J.Boundaryless] [T2Space N]

/-- **Pullback metrics along coverings are geodesically complete.** Let `f : M → N` be a smooth
covering map whose differential is everywhere invertible, and `g` a smooth Riemannian metric on
`N`. If every geodesic of `g` leaving `f x` is defined for all time, then so is every geodesic of
the pullback metric `f^* g` leaving `x`. -/
theorem isGeodesicallyCompleteAt_pullback_of_isCoveringMap
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
smooth covering map out of a connected Hausdorff manifold whose differential is everywhere
invertible, and `g` a smooth Riemannian metric on `N` all of whose geodesics are defined for all
time (equivalently, by the Hopf–Rinow theorem, `N` is complete on each connected component). Then
`M` is complete for the Riemannian distance of the pullback metric `f^* g`. -/
theorem completeSpace_pullback_of_isCoveringMap [T2Space M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible)
    (hcov : IsCoveringMap f)
    (h : letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
      ∀ y : N, IsGeodesicallyCompleteAt J N y) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
    letI : MetricSpace M :=
      haveI := Manifold.t3Space M I
      haveI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
        (F := E) (V := fun x : M ↦ TangentSpace I x)
      MetricSpace.ofRiemannianMetric I M
    CompleteSpace M := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  have := Manifold.t3Space M I
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun x : M ↦ TangentSpace I x)
  let : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  have : IsRiemannianManifold I M := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨x⟩ := ‹ConnectedSpace M›.toNonempty
  exact (Manifold.completeSpace_iff_isGeodesicallyCompleteAt x).2
    (g.isGeodesicallyCompleteAt_pullback_of_isCoveringMap hf hinv hcov (h (f x)))

end Bundle.ContMDiffRiemannianMetric
