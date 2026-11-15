/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Covering.Universal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# The Riemannian universal cover

Let `g` be a smooth Riemannian metric on a smooth manifold `M`, which is locally path-connected
and semilocally simply connected (as every manifold is), and let `x₀ ∈ M`. The projection
`p : UniversalCover x₀ → M` of the based-path universal cover, with the atlas pulled back along
`p`, is a smooth local diffeomorphism, so its differential is invertible at every point. Hence
the pullback `p^* g`, given by `(p^* g)(v, w) = g(dp v, dp w)`, is a smooth Riemannian metric on
the universal cover (`TauCeti.UniversalCover.pullbackMetric`), and `p` is a local Riemannian
isometry from `p^* g` to `g` (`TauCeti.UniversalCover.isLocalRiemannianIsometry_proj`). In
particular `p` preserves scalar and sectional curvature
(`TauCeti.UniversalCover.scalarCurvature_pullbackMetric`,
`TauCeti.UniversalCover.sectionalCurvature_pullbackMetric`).

## References

* John M. Lee, *Introduction to Riemannian Manifolds*, second edition, Graduate Texts in
  Mathematics 176, Springer, 2018, Chapter 2 (Riemannian coverings) and Proposition 7.6.
-/

public section

open Bundle Manifold
open scoped ContDiff

namespace TauCeti.UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] {x₀ : M}

omit [FiniteDimensional ℝ E] in
variable (I) in
/-- The projection of the universal cover is smooth of order `∞ + 1`, the regularity required to
pull back a smooth metric. -/
theorem contMDiff_proj_top_add_one : ContMDiff I I (∞ + 1) (proj : UniversalCover x₀ → M) :=
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  contMDiff_proj x₀

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
variable (I) in
/-- The differential of the projection of the universal cover is invertible at every point. -/
theorem isInvertible_mfderiv_proj (z : UniversalCover x₀) :
    (mfderiv I I (proj : UniversalCover x₀ → M) z).IsInvertible :=
  (isLocalDiffeomorph_proj (I := I) (n := ∞) x₀).isInvertible_mfderiv (by simp) z

/-- The pullback `p^* g` of a smooth Riemannian metric `g` on the base along the projection `p` of
the universal cover: `(p^* g)(v, w) = g(dp v, dp w)`. -/
noncomputable def pullbackMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    ContMDiffRiemannianMetric I ∞ E (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
  g.pullback proj (contMDiff_proj_top_add_one I) fun z ↦ (isInvertible_mfderiv_proj I z).injective

/-- The pullback metric on the universal cover applies the base metric to the images of the two
tangent vectors under the differential of the projection. -/
@[simp]
theorem pullbackMetric_inner (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) (v w : TangentSpace I z) :
    (pullbackMetric g).inner z v w =
      g.inner (proj z) (mfderiv I I (proj : UniversalCover x₀ → M) z v)
        (mfderiv I I (proj : UniversalCover x₀ → M) z w) :=
  g.pullback_inner _ _ _ z v w

/-- The projection of the universal cover is a local Riemannian isometry from the pullback metric
`p^* g` to `g`. -/
theorem isLocalRiemannianIsometry_proj
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(pullbackMetric g).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsLocalRiemannianIsometry I I (proj : UniversalCover x₀ → M) :=
  g.isLocalRiemannianIsometry_pullback_of_isInvertible _ (isInvertible_mfderiv_proj I)

variable [T2Space M]

/-- The scalar curvature of the pullback metric on the universal cover at `z` is the scalar
curvature of the base metric at the projection of `z`. -/
@[simp]
theorem scalarCurvature_pullbackMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) :
    (pullbackMetric g).scalarCurvature z = g.scalarCurvature (proj z) :=
  g.scalarCurvature_pullback_of_isInvertible _ (isInvertible_mfderiv_proj I) z

/-- The sectional curvature of the pullback metric on the universal cover on the plane spanned by
`u, v` at `z` is the sectional curvature of the base metric on the plane spanned by their images
under the differential of the projection. -/
theorem sectionalCurvature_pullbackMetric
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (z : UniversalCover x₀) (u v : TangentSpace I z) :
    (letI : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(pullbackMetric g).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I (UniversalCover x₀)).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) z u v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).sectionalCurvature
        (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (proj z)
        (mfderiv I I (proj : UniversalCover x₀ → M) z u)
        (mfderiv I I (proj : UniversalCover x₀ → M) z v)) :=
  g.sectionalCurvature_pullback_of_isInvertible _ (isInvertible_mfderiv_proj I) z u v

end TauCeti.UniversalCover
