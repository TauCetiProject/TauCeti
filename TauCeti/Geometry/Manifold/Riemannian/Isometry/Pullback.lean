/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Pullback

/-!
# Pulling a smooth metric back along a diffeomorphism

Let `Φ : M → N` be a diffeomorphism and `g` a smooth Riemannian metric on `N`. The pullback
metric `Φ^* g` on `M` (`Bundle.ContMDiffRiemannianMetric.pullback`) is the metric for which `Φ`
becomes a Riemannian isometry `(M, Φ^* g) → (N, g)`. Every curvature quantity is natural under
Riemannian isometries, so the curvature of `Φ^* g` at `x` is the curvature of `g` at `Φ x`. In
particular the scalar curvature satisfies `Scal(Φ^* g) = Scal(g) ∘ Φ`; this is the
diffeomorphism-invariance used for positive scalar curvature metrics. Since curvature is natural
under local Riemannian isometries, the same formula holds along any smooth map whose differential
is invertible at every point, such as a reparametrisation of the `ℝ` factor of `M × ℝ`.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.pullbackRiemannianIsometry`: a diffeomorphism `Φ` as a
  Riemannian isometry from the pulled-back metric `Φ^* g` to `g`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_pullback_of_isInvertible`: the scalar
  curvature of `f^* g` at `x` is the scalar curvature of `g` at `f x`, for any smooth map `f` whose
  differential is invertible at every point.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_pullback`: in particular, along a
  diffeomorphism `Φ`, `Scal(Φ^* g) = Scal(g) ∘ Φ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 2 (pullback metrics) and Proposition 7.6 (naturality of curvature).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

section Isometry

variable [IsManifold I 1 M] [IsManifold J 1 N] {n : ℕ∞ω}

/-- A diffeomorphism `Φ : M → N` is a Riemannian isometry from the metric `Φ^* g` pulled back
along `Φ` to the metric `g` on `N`. -/
def pullbackRiemannianIsometry (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
    TauCeti.RiemannianIsometry I J M N :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
  letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  { toDiffeomorph := Φ
    inner_mfderiv' := fun x v w ↦ (g.pullback_inner Φ hf hinj x v w).symm }

/-- The underlying diffeomorphism of `pullbackRiemannianIsometry g Φ` is `Φ`. -/
@[simp]
theorem toDiffeomorph_pullbackRiemannianIsometry
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
    (g.pullbackRiemannianIsometry Φ hf hinj).toDiffeomorph = Φ := by
  rfl

/-- As a function, `pullbackRiemannianIsometry g Φ` is `Φ`. -/
@[simp]
theorem coe_pullbackRiemannianIsometry
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (n + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.pullback Φ hf hinj).toRiemannianMetric⟩
    letI : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
    ⇑(g.pullbackRiemannianIsometry Φ hf hinj) = Φ := by
  rfl

end Isometry

variable [FiniteDimensional ℝ F] [T2Space M] [T2Space N] [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **Scalar curvature of a pullback along a local diffeomorphism.** If the differential of a
smooth map `f` is invertible at every point, the scalar curvature of `f^* g` at `x` is the scalar
curvature of `g` at `f x`. -/
theorem scalarCurvature_pullback_of_isInvertible
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)) {f : M → N}
    (hf : ContMDiff I J (∞ + 1) f) (hinv : ∀ x, (mfderiv I J f x).IsInvertible) (x : M) :
    (g.pullback f hf fun x ↦ (hinv x).injective).scalarCurvature x = g.scalarCurvature (f x) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.pullback f hf fun x ↦ (hinv x).injective).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun y : N ↦ TangentSpace J y) := ⟨g.toRiemannianMetric⟩
  have hloc : TauCeti.IsLocalRiemannianIsometry I J f :=
    { contMDiff := hf.of_le le_self_add
      isInvertible_mfderiv := hinv
      inner_mfderiv := fun x v w ↦ (g.pullback_inner f hf _ x v w).symm }
  rw [scalarCurvature_def, scalarCurvature_def, hloc.scalarCurvature_map x]

/-- **Diffeomorphism invariance of scalar curvature.** The scalar curvature of the metric
`Φ^* g` pulled back along a diffeomorphism `Φ` is the scalar curvature of `g` composed with `Φ`. -/
@[simp]
theorem scalarCurvature_pullback
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) (x : M) :
    (g.pullback Φ hf hinj).scalarCurvature x = g.scalarCurvature (Φ x) :=
  scalarCurvature_pullback_of_isInvertible g hf (fun _ ↦ Φ.isInvertible_mfderiv (by simp)) x

end Bundle.ContMDiffRiemannianMetric
