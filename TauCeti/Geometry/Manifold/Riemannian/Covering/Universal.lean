/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.UniversalCover
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

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

## References

* John M. Lee, *Introduction to Riemannian Manifolds*, second edition, Graduate Texts in
  Mathematics 176, Springer, 2018, Chapter 2 (Riemannian coverings) and Proposition 7.6.
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
    let : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
      ⟨(g.universalCover x₀).toRiemannianMetric⟩
    let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (proj : UniversalCover x₀ → M) := by
  let : RiemannianBundle (fun z : UniversalCover x₀ ↦ TangentSpace I z) :=
    ⟨(g.universalCover x₀).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact
    { contMDiff := TauCeti.UniversalCover.contMDiff_proj x₀
      isInvertible_mfderiv := isInvertible_mfderiv_proj (I := I)
      inner_mfderiv := fun z v w ↦ (g.universalCover_inner z v w).symm }

end Metric

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
