/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Naturality of the Riemannian gradient under local isometries

The differential of a local Riemannian isometry carries the gradient of a pulled-back real
function to its target gradient, and preserves its norm. Differentiability is required
only at the target point. Consequently the pointwise inner product `⟪∇u, ∇v⟫` of two
gradients, the integrand of the Dirichlet energy, is natural:
`⟪∇(u ∘ f), ∇(v ∘ f)⟫ = ⟪∇u, ∇v⟫ ∘ f`.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.
-/

public noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti.IsLocalRiemannianIsometry

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] {f : M → N}

/-- A local isometry carries the gradient of a pullback to the target gradient, under
pointwise differentiability of the target function. -/
@[simp]
theorem mfderiv_mgradient_comp (hf : IsLocalRiemannianIsometry I J f)
    {φ : N → ℝ} {x : M} (hφ : MDifferentiableAt J 𝓘(ℝ) φ (f x)) :
    mfderiv I J f x (mgradient I (φ ∘ f) x) = mgradient J φ (f x) := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨w, rfl⟩ := hf.mfderiv_surjective x v
  rw [hf.inner_mfderiv, inner_mgradient_comp hφ (hf.mdifferentiableAt x)]

/-- A local isometry pulls back the pointwise inner product of two gradients:
`⟪∇(φ ∘ f), ∇(ψ ∘ f)⟫ = ⟪∇φ, ∇ψ⟫ ∘ f`. -/
theorem inner_mgradient_comp_comp (hf : IsLocalRiemannianIsometry I J f)
    {φ ψ : N → ℝ} {x : M} (hφ : MDifferentiableAt J 𝓘(ℝ) φ (f x))
    (hψ : MDifferentiableAt J 𝓘(ℝ) ψ (f x)) :
    inner ℝ (mgradient I (φ ∘ f) x) (mgradient I (ψ ∘ f) x) =
      inner ℝ (mgradient J φ (f x)) (mgradient J ψ (f x)) := by
  rw [← hf.inner_mfderiv, hf.mfderiv_mgradient_comp hφ, hf.mfderiv_mgradient_comp hψ]

/-- A local isometry preserves the norm of the gradient of a pulled-back function. -/
theorem norm_mgradient_comp (hf : IsLocalRiemannianIsometry I J f)
    {φ : N → ℝ} {x : M} (hφ : MDifferentiableAt J 𝓘(ℝ) φ (f x)) :
    ‖mgradient I (φ ∘ f) x‖ = ‖mgradient J φ (f x)‖ := by
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  rw [← e.norm_map, he, hf.mfderiv_mgradient_comp hφ]

end TauCeti.IsLocalRiemannianIsometry
