/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Homeomorphisms of model spaces induced by linear equivalences

Two models with corners `I : ModelWithCorners 𝕜 E H` and `I₁ : ModelWithCorners 𝕜 E₁ H₁` on
different model spaces may be related by a continuous linear equivalence `A : E ≃L[𝕜] E₁`
carrying the range of `I` onto the range of `I₁`. Then `h ↦ I₁.symm (A (I h))` is a
homeomorphism `ContinuousLinearEquiv.modelHomeomorph A hA : H ≃ₜ H₁`, which reads as `A` through
the two models and is smooth in both directions at every regularity. The basic example is the
product of a boundaryless model with the half-line, which is linearly the half-space model one
dimension up.

Because of this, charts can be moved between manifolds with the two models: a chart in the
maximal atlas of `M`, pulled back along a diffeomorphism `e : M₁ ≃ₘ M` and followed by
`modelHomeomorph`, lies in the maximal atlas of `M₁`
(`ContinuousLinearEquiv.transHomeomorph_modelHomeomorph_mem_maximalAtlas`).

This complements Mathlib's `ModelWithCorners.transContinuousLinearEquiv`, which changes the
vector-space coordinates of a single model while keeping its model space.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for models of
  manifolds with boundary and their changes of coordinates.
-/

public section

noncomputable section

namespace ContinuousLinearEquiv

open Manifold Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {H : Type*} [TopologicalSpace H] {H₁ : Type*} [TopologicalSpace H₁]
  {I : ModelWithCorners 𝕜 E H} {I₁ : ModelWithCorners 𝕜 E₁ H₁}

/-- A continuous linear equivalence `A : E ≃L E₁` carrying the range of `I` onto the range of
`I₁` induces the homeomorphism `h ↦ I₁.symm (A (I h))` of the model spaces. -/
def modelHomeomorph (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁) : H ≃ₜ H₁ where
  toFun h := I₁.symm (A (I h))
  invFun h := I.symm (A.symm (I₁ h))
  left_inv h := by
    have hmem : A (I h) ∈ range I₁ := hA ▸ mem_image_of_mem A (mem_range_self h)
    simp [I₁.right_inv hmem]
  right_inv h := by
    have hmem : A.symm (I₁ h) ∈ range I := by
      obtain ⟨v, hv, hv'⟩ := (hA ▸ mem_range_self h : I₁ h ∈ A '' range I)
      rw [← hv', ContinuousLinearEquiv.symm_apply_apply]
      exact hv
    simp [I.right_inv hmem]
  continuous_toFun := I₁.continuous_symm.comp (A.continuous.comp I.continuous)
  continuous_invFun := I.continuous_symm.comp (A.symm.continuous.comp I₁.continuous)

/-- `modelHomeomorph A hA` sends `h` to `I₁.symm (A (I h))`. -/
theorem modelHomeomorph_apply (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁) (h : H) :
    A.modelHomeomorph hA h = I₁.symm (A (I h)) := by
  rfl

/-- The inverse of `modelHomeomorph A hA` sends `h` to `I.symm (A.symm (I₁ h))`. -/
theorem modelHomeomorph_symm_apply (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁) (h : H₁) :
    (A.modelHomeomorph hA).symm h = I.symm (A.symm (I₁ h)) := by
  rfl

/-- Read through the models, `modelHomeomorph A hA` is `A`. -/
@[simp]
theorem model_modelHomeomorph (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁) (h : H) :
    I₁ (A.modelHomeomorph hA h) = A (I h) :=
  I₁.right_inv (hA ▸ mem_image_of_mem A (mem_range_self h))

/-- Read through the models, the inverse of `modelHomeomorph A hA` is `A.symm`. -/
@[simp]
theorem model_modelHomeomorph_symm (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁)
    (h : H₁) : I ((A.modelHomeomorph hA).symm h) = A.symm (I₁ h) := by
  have := model_modelHomeomorph A hA ((A.modelHomeomorph hA).symm h)
  rw [Homeomorph.apply_symm_apply] at this
  rw [this, ContinuousLinearEquiv.symm_apply_apply]

/-- The homeomorphism of model spaces induced by a linear equivalence is smooth at every
regularity. -/
theorem contMDiff_modelHomeomorph {n : ℕ∞ω} (A : E ≃L[𝕜] E₁)
    (hA : A '' range I = range I₁) : ContMDiff I I₁ n (A.modelHomeomorph hA) := by
  have hrange : ∀ h, A (I h) ∈ range I₁ := fun h ↦ hA ▸ mem_image_of_mem A (mem_range_self h)
  exact (I₁.contMDiffOn_symm.comp_contMDiff (A.contDiff.contMDiff.comp I.contMDiff) hrange).congr
    fun _ ↦ rfl

/-- The inverse of the homeomorphism of model spaces induced by a linear equivalence is smooth
at every regularity. -/
theorem contMDiff_modelHomeomorph_symm {n : ℕ∞ω} (A : E ≃L[𝕜] E₁)
    (hA : A '' range I = range I₁) : ContMDiff I₁ I n (A.modelHomeomorph hA).symm := by
  have hA' : A.symm '' range I₁ = range I := by
    rw [← hA, ← image_comp]
    simp
  have hrange : ∀ h, A.symm (I₁ h) ∈ range I :=
    fun h ↦ hA' ▸ mem_image_of_mem A.symm (mem_range_self h)
  exact (I.contMDiffOn_symm.comp_contMDiff (A.symm.contDiff.contMDiff.comp I₁.contMDiff)
    hrange).congr fun _ ↦ rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] {n m : ℕ∞ω}

/-- A chart of `M` in the maximal atlas, pulled back along a `C^m` diffeomorphism
`e : M₁ ≃ₘ M` and followed by the homeomorphism of model spaces induced by `A`, is a chart of
`M₁` in the maximal atlas at any regularity `n ≤ m`. -/
theorem transHomeomorph_modelHomeomorph_mem_maximalAtlas [IsManifold I₁ n M₁]
    (A : E ≃L[𝕜] E₁) (hA : A '' range I = range I₁) (e : M₁ ≃ₘ^m⟮I₁, I⟯ M) (hnm : n ≤ m)
    {φ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas I n M) :
    (e.toHomeomorph.transOpenPartialHomeomorph φ).transHomeomorph (A.modelHomeomorph hA) ∈
      IsManifold.maximalAtlas I₁ n M₁ := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · exact (contMDiff_modelHomeomorph A hA).comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hφ).comp (e.contMDiff.of_le hnm).contMDiffOn
        fun _ hx ↦ hx)
  · exact (e.symm.contMDiff.of_le hnm).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).comp
        (contMDiff_modelHomeomorph_symm A hA).contMDiffOn fun _ hx ↦ hx)

end ContinuousLinearEquiv
