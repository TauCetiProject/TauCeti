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
function to its target gradient. Differentiability is required only at the target point.

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

end TauCeti.IsLocalRiemannianIsometry
