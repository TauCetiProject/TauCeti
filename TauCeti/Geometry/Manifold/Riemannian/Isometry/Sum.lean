/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Sum
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Curvature of a disjoint union of Riemannian manifolds

Let `g₁` and `g₂` be smooth Riemannian metrics on manifolds `M` and `M'` modelled on the same
space, and let `g₁ ⊔ g₂` be the metric on the disjoint union `M ⊕ M'` which is `g₁` on `M` and `g₂`
on `M'` (`Bundle.ContMDiffRiemannianMetric.sumTangentSpace`). The inclusions of `M` and `M'` into
`M ⊕ M'` are local Riemannian isometries, so every curvature quantity of `g₁ ⊔ g₂` at a point of a
summand is that of the metric of the summand. In particular the scalar curvature of `g₁ ⊔ g₂` is
`Scal(g₁)` on `M` and `Scal(g₂)` on `M'`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_sumInl` and
  `Bundle.ContMDiffRiemannianMetric.isLocalRiemannianIsometry_sumInr`: the inclusions of the
  summands are local Riemannian isometries.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_sumTangentSpace_inl` and
  `Bundle.ContMDiffRiemannianMetric.scalarCurvature_sumTangentSpace_inr`: the scalar curvature of
  the disjoint union metric on each summand is that of the metric of the summand.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (local isometries) and Proposition 7.6 (naturality of the curvature tensor).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']

section LocalIsometry

variable [IsManifold I 1 M] [IsManifold I 1 M'] {n : ℕ∞ω}
  (g₁ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric I n E (fun x : M' ↦ TangentSpace I x))

/-- The inclusion of `M` into `M ⊕ M'` is a local Riemannian isometry from `g₁` to the disjoint
union of `g₁` and `g₂`. -/
theorem isLocalRiemannianIsometry_sumInl :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
    letI : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
      ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (Sum.inl : M → M ⊕ M') :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  letI : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
    ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
  { contMDiff := ContMDiff.inl
    isInvertible_mfderiv := fun x ↦ by
      rw [mfderiv_sumInl (p := Sum.inl x)]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    inner_mfderiv := fun x v w ↦ by
      rw [mfderiv_sumInl (p := Sum.inl x), inner_riemannianBundle (g₁.sumTangentSpace g₂),
        inner_riemannianBundle g₁]
      -- The differential of the inclusion is the identity of the model space `E`.
      exact g₁.sumTangentSpace_inner_inl g₂ x v w }

/-- The inclusion of `M'` into `M ⊕ M'` is a local Riemannian isometry from `g₂` to the disjoint
union of `g₁` and `g₂`. -/
theorem isLocalRiemannianIsometry_sumInr :
    letI : RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g₂.toRiemannianMetric⟩
    letI : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
      ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I I (Sum.inr : M' → M ⊕ M') :=
  letI : RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g₂.toRiemannianMetric⟩
  letI : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
    ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
  { contMDiff := ContMDiff.inr
    isInvertible_mfderiv := fun x ↦ by
      rw [mfderiv_sumInr (M := M) (q' := x)]
      exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
    inner_mfderiv := fun x v w ↦ by
      rw [mfderiv_sumInr (M := M) (q' := x), inner_riemannianBundle (g₁.sumTangentSpace g₂),
        inner_riemannianBundle g₂]
      -- The differential of the inclusion is the identity of the model space `E`.
      exact g₁.sumTangentSpace_inner_inr g₂ x v w }

end LocalIsometry

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [T2Space M'] [IsManifold I ∞ M']
  (g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
  (g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M' ↦ TangentSpace I x))

/-- The scalar curvature of the disjoint union of metrics `g₁` and `g₂` at a point of `M` is the
scalar curvature of `g₁` there. -/
@[simp]
theorem scalarCurvature_sumTangentSpace_inl (x : M) :
    (g₁.sumTangentSpace g₂).scalarCurvature (Sum.inl x) = g₁.scalarCurvature x := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
    ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
  rw [scalarCurvature_def, scalarCurvature_def,
    (g₁.isLocalRiemannianIsometry_sumInl g₂).scalarCurvature_map x]

/-- The scalar curvature of the disjoint union of metrics `g₁` and `g₂` at a point of `M'` is the
scalar curvature of `g₂` there. -/
@[simp]
theorem scalarCurvature_sumTangentSpace_inr (y : M') :
    (g₁.sumTangentSpace g₂).scalarCurvature (Sum.inr y) = g₂.scalarCurvature y := by
  let _ : RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g₂.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun p : M ⊕ M' ↦ TangentSpace I p) :=
    ⟨(g₁.sumTangentSpace g₂).toRiemannianMetric⟩
  rw [scalarCurvature_def, scalarCurvature_def,
    (g₁.isLocalRiemannianIsometry_sumInr g₂).scalarCurvature_map y]

end Bundle.ContMDiffRiemannianMetric
