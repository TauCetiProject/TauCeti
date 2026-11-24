/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Naturality of the Riemannian gradient under local isometries

The differential of a local Riemannian isometry carries the gradient of a pulled-back real
function to its target gradient, and preserves its norm. Differentiability is required
only at the target point. Consequently the pointwise inner product `⟪∇u, ∇v⟫` of two
gradients, the integrand of the Dirichlet energy, is natural:
`⟪∇(u ∘ f), ∇(v ∘ f)⟫ = ⟪∇u, ∇v⟫ ∘ f`.

A local isometry `f` of `M` that preserves a function `φ`, `φ ∘ f = φ`, therefore carries the
negative gradient field of `φ` to itself, and so carries negative gradient trajectories of `φ` to
negative gradient trajectories
(`TauCeti.IsLocalRiemannianIsometry.isMIntegralCurve_comp_neg_mgradient`). By uniqueness of
integral curves, a trajectory through a fixed point of `f` consists of fixed points of `f`
(`TauCeti.IsLocalRiemannianIsometry.apply_eq_of_isMIntegralCurve_neg_mgradient`): symmetries of
`φ` and of the metric confine its gradient flow to their fixed point sets.

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

section Symmetry

variable {f : M → M} {φ : M → ℝ} {γ : ℝ → M}

/-- **A symmetry carries negative gradient trajectories to negative gradient trajectories.** A
local isometry `f` of `M` with `φ ∘ f = φ` sends every global integral curve of `-grad φ` to one. -/
theorem isMIntegralCurve_comp_neg_mgradient (hf : IsLocalRiemannianIsometry I I f)
    (hφ : MDifferentiable I 𝓘(ℝ) φ) (hφf : ∀ x, φ (f x) = φ x)
    (hγ : IsMIntegralCurve γ (-mgradient I φ)) : IsMIntegralCurve (f ∘ γ) (-mgradient I φ) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  refine hγ.map_of_mfderiv_eq (fun t _ ↦ hf.mdifferentiableAt (γ t)) fun t _ ↦ ?_
  have h := hf.mfderiv_mgradient_comp (hφ (f (γ t))) (x := γ t)
  rw [show φ ∘ f = φ from funext hφf] at h
  simp only [Pi.neg_apply, map_neg, h]

/-- **Negative gradient trajectories through fixed points of a symmetry stay fixed.** Let `f` be a
local isometry of a Hausdorff boundaryless manifold with a `C¹` metric, and `φ` a `C²` function
with `φ ∘ f = φ`. If a global integral curve `γ` of `-grad φ` passes through a fixed point of `f`,
then every point of `γ` is fixed by `f`. -/
theorem apply_eq_of_isMIntegralCurve_neg_mgradient [IsManifold I 2 M] [T2Space M]
    [BoundarylessManifold I M] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
    (hf : IsLocalRiemannianIsometry I I f) (hφ : ContMDiff I 𝓘(ℝ) 2 φ)
    (hφf : ∀ x, φ (f x) = φ x) (hγ : IsMIntegralCurve γ (-mgradient I φ)) {t₀ : ℝ}
    (h₀ : f (γ t₀) = γ t₀) (t : ℝ) : f (γ t) = γ t :=
  congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (contMDiff_neg_mgradient_one hφ)
    (hf.isMIntegralCurve_comp_neg_mgradient (hφ.mdifferentiable two_ne_zero) hφf hγ) hγ
    (t₀ := t₀) h₀) t

end Symmetry

end TauCeti.IsLocalRiemannianIsometry
