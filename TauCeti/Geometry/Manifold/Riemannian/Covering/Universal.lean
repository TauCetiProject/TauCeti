/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.UniversalCover
public import TauCeti.Geometry.Manifold.Riemannian.Covering.Complete

/-!
# The Riemannian universal cover

Let `g` be a `C^n` Riemannian metric on a `C¹` manifold `M`, which is locally path-connected
and semilocally simply connected (as every manifold is), and let `x₀ ∈ M`. The projection
`p : UniversalCover x₀ → M` of the based-path universal cover, with the atlas pulled back along
`p`, is a local diffeomorphism with invertible differential at every point. Hence
the pullback `p^* g`, given by `(p^* g)(v, w) = g(dp v, dp w)`, is a `C^n` Riemannian metric on
the universal cover (`Bundle.ContMDiffRiemannianMetric.universalCover`), and `p` is a local
Riemannian isometry from `p^* g` to `g`
(`Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_universalCoverProj`).
For a smooth metric on a smooth Hausdorff manifold, `p` also preserves scalar and sectional
curvature
(`Bundle.ContMDiffRiemannianMetric.scalarCurvature_universalCover`,
`Bundle.ContMDiffRiemannianMetric.sectionalCurvature_universalCover`).
For a smooth metric on a boundaryless manifold, geodesic completeness is equivalent at
corresponding points
(`Bundle.ContMDiffRiemannianMetric.isGeodesicallyCompleteAt_universalCover_iff`).
If the model is boundaryless and the base is Hausdorff, geodesic completeness at the basepoint
makes the induced Riemannian distance upstairs complete
(`Bundle.ContMDiffRiemannianMetric.completeSpace_universalCover`).

For a base metric supplied by `RiemannianBundle`, `open scoped TauCeti` installs the
pullback bundle on `UniversalCover x₀`, together with its inherited continuity and `C^n`
regularity. `TauCeti.UniversalCover.inner_tangentSpace` characterizes its inner product, and
`TauCeti.UniversalCover.isLocalRiemannianIsometry_proj` gives the projection's local-isometry
property with the base's original metric instance.

## References

* John M. Lee, *Introduction to Riemannian Manifolds*, second edition, Graduate Texts in
  Mathematics 176, Springer, 2018, Chapter 2 (Riemannian coverings), Chapter 6 (completeness)
  and Proposition 7.6.
-/

public section

open Bundle Manifold
open scoped ContDiff

open TauCeti (UniversalCover SemilocallySimplyConnectedSpace)
open TauCeti.UniversalCover

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] {x₀ : M}

section Metric

variable [IsManifold I 1 M] {n : ℕ∞ω}

/-- The pullback `p^* g` of a `C^n` Riemannian metric `g` on the base along the projection `p` of
the universal cover: `(p^* g)(v, w) = g(dp v, dp w)`. -/
noncomputable def universalCover
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    ContMDiffRiemannianMetric I n E (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
  g.pullback proj (TauCeti.UniversalCover.contMDiff_proj x₀)
    fun z ↦ (isInvertible_mfderiv_proj (I := I) z).injective

/-- The metric on the universal cover is the pullback along the projection. -/
theorem universalCover_eq_pullback
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    g.universalCover x₀ =
      g.pullback proj (TauCeti.UniversalCover.contMDiff_proj x₀)
        fun z ↦ (isInvertible_mfderiv_proj (I := I) z).injective := (rfl)

/-- The pullback metric on the universal cover applies the base metric to the images of the two
tangent vectors under the differential of the projection. -/
@[simp]
theorem universalCover_inner (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) (v w : TangentSpace I z) :
    (g.universalCover x₀).inner z v w =
      g.inner (proj z) (mfderiv I I (proj : UniversalCover x₀ → M) z v)
        (mfderiv I I (proj : UniversalCover x₀ → M) z w) := by
  rw [universalCover_eq_pullback]
  exact g.pullback_inner _ _ _ z v w

/-- The projection of the universal cover is a local Riemannian isometry from the pullback metric
`p^* g` to `g`. -/
theorem isLocalRiemannianIsometry_universalCoverProj
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (proj : UniversalCover x₀ → M) := by
  let : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
    ⟨(g.universalCover x₀).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact
    { contMDiff := TauCeti.UniversalCover.contMDiff_proj x₀
      isInvertible_mfderiv := isInvertible_mfderiv_proj (I := I)
      inner_mfderiv := fun z v w ↦ (g.universalCover_inner z v w).symm }

end Metric

section Completeness

variable [IsManifold I ∞ M]

/-- Geodesic completeness for the universal-cover metric at a point is equivalent to geodesic
completeness for the base metric at its projection. -/
theorem isGeodesicallyCompleteAt_universalCover_iff [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) :
    (letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩;
      TauCeti.Manifold.IsGeodesicallyCompleteAt I (UniversalCover x₀) z) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      TauCeti.Manifold.IsGeodesicallyCompleteAt I M (proj z)) := by
  let : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
    ⟨(g.universalCover x₀).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ((g.isLocalRiemannianIsometry_universalCoverProj x₀
    ).isGeodesicallyCompleteAt_iff_of_isCoveringMap (isCoveringMap x₀) z).symm

/-- Geodesic completeness at the basepoint makes the universal cover complete for the
Riemannian distance of its pullback metric. -/
theorem completeSpace_universalCover [I.Boundaryless] [T2Space M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M)
    (h : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      TauCeti.Manifold.IsGeodesicallyCompleteAt I M x₀) :
    letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩
    letI : MetricSpace (UniversalCover x₀) :=
      haveI := Manifold.locallyCompact_of_finiteDimensional (M := UniversalCover x₀) I
      haveI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
        (F := E) (V := fun z : UniversalCover x₀ ↦ TangentSpace I z)
      TauCeti.MetricSpace.ofRiemannianMetric I (UniversalCover x₀)
    CompleteSpace (UniversalCover x₀) := by
  let : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
    ⟨(g.universalCover x₀).toRiemannianMetric⟩
  have := Manifold.locallyCompact_of_finiteDimensional (M := UniversalCover x₀) I
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
    (F := E) (V := fun z : UniversalCover x₀ ↦ TangentSpace I z)
  let : MetricSpace (UniversalCover x₀) :=
    TauCeti.MetricSpace.ofRiemannianMetric I (UniversalCover x₀)
  apply (TauCeti.Manifold.completeSpace_iff_isGeodesicallyCompleteAt
    (I := I) (basepointLift x₀ : UniversalCover x₀)).2
  exact (g.isGeodesicallyCompleteAt_universalCover_iff (basepointLift x₀ : UniversalCover x₀)).2
    (by simpa only [proj_basepointLift] using h)

end Completeness

variable [T2Space M] [IsManifold I ∞ M]

/-- The scalar curvature of the pullback metric on the universal cover at `z` is the scalar
curvature of the base metric at the projection of `z`. -/
@[simp]
theorem scalarCurvature_universalCover
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) :
    (g.universalCover x₀).scalarCurvature z = g.scalarCurvature (proj z) := by
  rw [universalCover_eq_pullback]
  exact g.scalarCurvature_pullback_of_isInvertible _ (isInvertible_mfderiv_proj (I := I)) z

/-- The sectional curvature of the pullback metric on the universal cover on the plane spanned by
`u, v` at `z` is the sectional curvature of the base metric on the plane spanned by their images
under the differential of the projection. -/
theorem sectionalCurvature_universalCover
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) (u v : TangentSpace I z) :
    (letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I (UniversalCover x₀)).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) z u v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (proj z)
        (mfderiv I I (proj : UniversalCover x₀ → M) z u)
        (mfderiv I I (proj : UniversalCover x₀ → M) z v)) := by
  rw [universalCover_eq_pullback]
  exact g.sectionalCurvature_pullback_of_isInvertible _ (isInvertible_mfderiv_proj (I := I)) z u v

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The universal cover inherits the base metric by pullback along the projection differential.
Use `open scoped TauCeti` to install this Riemannian bundle. -/
@[instance_reducible]
noncomputable def instRiemannianBundle (x₀ : M) :
    RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
  let g : RiemannianMetric (fun x : M ↦ TangentSpace I x) := RiemannianBundle.g
  ⟨{ inner z := (ContinuousLinearMap.precomp ℝ (mfderiv I I proj z)).comp
        ((g.inner (proj z)).comp (mfderiv I I proj z))
     symm z v w := g.symm (proj z) _ _
     pos z v hv := g.pos (proj z) _
       ((map_ne_zero_iff (mfderiv I I proj z)
         (isInvertible_mfderiv_proj (I := I) z).injective).2 hv)
     continuousAt z := (g.continuousAt (proj z)).comp_of_eq
       (mfderiv I I proj z).continuous.continuousAt (map_zero _)
     isVonNBounded z := by
       refine ((g.isVonNBounded (proj z)).image
         (mfderiv I I proj z).inverse).subset ?_
       intro v hv
       exact ⟨mfderiv I I proj z v, hv,
         (isInvertible_mfderiv_proj (I := I) z).inverse_apply_self v⟩ }⟩

scoped[TauCeti] attribute [instance] instRiemannianBundle

open scoped TauCeti

/-- The inner product upstairs is the base inner product applied to the two projected vectors. -/
@[simp]
theorem inner_tangentSpace (x₀ : M) (z : UniversalCover x₀) (v w : TangentSpace I z) :
    inner ℝ v w = inner ℝ (mfderiv I I proj z v) (mfderiv I I proj z w) := (rfl)

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- The inherited Riemannian bundle is as `C^n` as the base bundle. -/
theorem instIsContMDiffRiemannianBundle {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (x₀ : M) :
    IsContMDiffRiemannianBundle I n E (fun z : UniversalCover x₀ ↦ TangentSpace I z) := by
  let g := (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := n) (F := E) (V := fun x : M ↦ TangentSpace I x)).universalCover x₀
  refine ⟨g.inner, g.contMDiff, ?_⟩
  intro z v w
  dsimp only [g]
  rw [Bundle.ContMDiffRiemannianMetric.universalCover_inner,
    Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  exact inner_tangentSpace x₀ z v w

scoped[TauCeti] attribute [instance] TauCeti.UniversalCover.instIsContMDiffRiemannianBundle

/-- The inherited Riemannian bundle is continuous when the base bundle is continuous. -/
theorem instIsContinuousRiemannianBundle
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (x₀ : M) :
    IsContinuousRiemannianBundle E (fun z : UniversalCover x₀ ↦ TangentSpace I z) := by
  let : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  have := TauCeti.UniversalCover.instIsContMDiffRiemannianBundle (I := I) (n := 0) x₀
  exact IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0)
    (F := E) (V := fun z : UniversalCover x₀ ↦ TangentSpace I z)

scoped[TauCeti] attribute [instance] TauCeti.UniversalCover.instIsContinuousRiemannianBundle

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] in
/-- The projection, with the inherited Riemannian bundle upstairs, is a local Riemannian
isometry to the base with its original Riemannian bundle. -/
theorem isLocalRiemannianIsometry_proj (x₀ : M) :
    IsLocalRiemannianIsometry I I (proj : UniversalCover x₀ → M) where
  contMDiff := contMDiff_proj x₀
  isInvertible_mfderiv := isInvertible_mfderiv_proj (I := I)
  inner_mfderiv z v w := (inner_tangentSpace x₀ z v w).symm

end TauCeti.UniversalCover
