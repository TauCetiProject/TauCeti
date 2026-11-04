/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Riemannian gradients and isometries

A local Riemannian isometry `f : M → N` transports the Riemannian gradient of a differentiable
scalar function `u : N → ℝ`: at each point `x`, the differential `df_x` maps `grad (u ∘ f) x` to
`grad u (f x)`, equivalently `f^* (grad u) = grad (u ∘ f)`. Consequently, pulling functions back
along `f` preserves pointwise inner products and norms of gradients.

For a global `TauCeti.RiemannianIsometry`, the underlying map is a diffeomorphism, so precomposing
with it preserves differentiability at every point (including on manifolds with boundary or
corners). All gradient transport identities therefore hold unconditionally without a
differentiability hypothesis on `u`: outside points of differentiability both gradients vanish.

## Main results

* `TauCeti.IsLocalRiemannianIsometry.mfderiv_mgradient_comp`,
  `TauCeti.IsLocalRiemannianIsometry.mpullback_mgradient`: gradient transport for differentiable
  functions along a local Riemannian isometry, together with
  `TauCeti.IsLocalRiemannianIsometry.inner_mgradient_comp` and
  `TauCeti.IsLocalRiemannianIsometry.norm_mgradient_comp`.
* `TauCeti.RiemannianIsometry.mfderiv_mgradient_comp`,
  `TauCeti.RiemannianIsometry.mpullback_mgradient`,
  `TauCeti.RiemannianIsometry.inner_mgradient_comp`,
  `TauCeti.RiemannianIsometry.norm_mgradient_comp`: the unconditional counterparts for a global
  Riemannian isometry.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

open Bundle Manifold TauCeti.Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

namespace IsLocalRiemannianIsometry

variable {f : M → N}

/-- The differential of a local Riemannian isometry maps the gradient of `u ∘ f` at `x` to the
gradient of `u` at `f x`, provided `u` is differentiable at `f x`. -/
theorem mfderiv_mgradient_comp (hf : IsLocalRiemannianIsometry I J f) {u : N → ℝ} {x : M}
    (hu : MDifferentiableAt J 𝓘(ℝ) u (f x)) :
    mfderiv I J f x (mgradient I (u ∘ f) x) = mgradient J u (f x) := by
  apply ext_inner_right ℝ
  intro w
  obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x w
  rw [hf.inner_mfderiv, TauCeti.Manifold.inner_mgradient_comp hu (hf.mdifferentiableAt x)]

/-- Pulling back the gradient of `u` along a local Riemannian isometry at `x` gives the gradient
of `u ∘ f` at `x`, provided `u` is differentiable at `f x`. -/
theorem mpullback_apply_mgradient (hf : IsLocalRiemannianIsometry I J f) {u : N → ℝ} {x : M}
    (hu : MDifferentiableAt J 𝓘(ℝ) u (f x)) :
    mpullback I J f (mgradient J u) x = mgradient I (u ∘ f) x :=
  (hf.mpullback_apply_eq_iff (mgradient J u) _).2 (hf.mfderiv_mgradient_comp hu).symm

/-- Pulling back the gradient of a differentiable function along a local Riemannian isometry gives
the gradient of the pulled-back function. -/
theorem mpullback_mgradient (hf : IsLocalRiemannianIsometry I J f) {u : N → ℝ}
    (hu : MDifferentiable J 𝓘(ℝ) u) :
    mpullback I J f (mgradient J u) = mgradient I (u ∘ f) :=
  funext fun x ↦ hf.mpullback_apply_mgradient (hu (f x))

/-- Pulling differentiable functions back along a local Riemannian isometry preserves the inner
product of their gradients. -/
theorem inner_mgradient_comp (hf : IsLocalRiemannianIsometry I J f) {u w : N → ℝ} {x : M}
    (hu : MDifferentiableAt J 𝓘(ℝ) u (f x)) (hw : MDifferentiableAt J 𝓘(ℝ) w (f x)) :
    inner ℝ (mgradient I (u ∘ f) x) (mgradient I (w ∘ f) x) =
      inner ℝ (mgradient J u (f x)) (mgradient J w (f x)) := by
  rw [← hf.inner_mfderiv x, hf.mfderiv_mgradient_comp hu, hf.mfderiv_mgradient_comp hw]

/-- Pulling a differentiable function back along a local Riemannian isometry preserves the norm of
its gradient. -/
theorem norm_mgradient_comp (hf : IsLocalRiemannianIsometry I J f) {u : N → ℝ} {x : M}
    (hu : MDifferentiableAt J 𝓘(ℝ) u (f x)) :
    ‖mgradient I (u ∘ f) x‖ = ‖mgradient J u (f x)‖ := by
  rw [← hf.mfderiv_mgradient_comp hu]
  obtain ⟨e, he⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  rw [← he, e.norm_map]

end IsLocalRiemannianIsometry

namespace RiemannianIsometry

/-- The differential of a Riemannian isometry maps the gradient of `u ∘ Φ` at `x` to the gradient
of `u` at `Φ x`. No differentiability hypothesis on `u` is needed: since `Φ` is a diffeomorphism,
`u ∘ Φ` is differentiable at `x` if and only if `u` is differentiable at `Φ x`, and otherwise both
gradients vanish. -/
@[simp]
theorem mfderiv_mgradient_comp (Φ : RiemannianIsometry I J M N) (u : N → ℝ) (x : M) :
    mfderiv I J Φ x (mgradient I (u ∘ Φ) x) = mgradient J u (Φ x) := by
  by_cases hu : MDifferentiableAt J 𝓘(ℝ) u (Φ x)
  · exact Φ.isLocalRiemannianIsometry.mfderiv_mgradient_comp hu
  · have huΦ : ¬MDifferentiableAt I 𝓘(ℝ) (u ∘ Φ) x := by
      simpa only [coe_toDiffeomorph] using
        (Φ.toDiffeomorph.mdifferentiableAt_comp_diffeomorph_iff (by simp)).not.2 hu
    have h0 : mgradient I (u ∘ Φ) x = 0 := by
      rw [mgradient_eq_zero_iff, mvfderiv, mfderiv_zero_of_not_mdifferentiableAt huΦ,
        ContinuousLinearMap.comp_zero]
    have h0' : mgradient J u (Φ x) = 0 := by
      rw [mgradient_eq_zero_iff, mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hu,
        ContinuousLinearMap.comp_zero]
    rw [h0, h0', map_zero]

/-- Pulling back the gradient of a function along a Riemannian isometry gives the gradient of the
pulled-back function. -/
@[simp]
theorem mpullback_mgradient (Φ : RiemannianIsometry I J M N) (u : N → ℝ) :
    mpullback I J Φ (mgradient J u) = mgradient I (u ∘ Φ) :=
  funext fun x ↦
    (Φ.isLocalRiemannianIsometry.mpullback_apply_eq_iff (mgradient J u) _).2
      (Φ.mfderiv_mgradient_comp u x).symm

/-- Pulling functions back along a Riemannian isometry preserves the inner product of their
gradients. -/
theorem inner_mgradient_comp (Φ : RiemannianIsometry I J M N) (u w : N → ℝ) (x : M) :
    inner ℝ (mgradient I (u ∘ Φ) x) (mgradient I (w ∘ Φ) x) =
      inner ℝ (mgradient J u (Φ x)) (mgradient J w (Φ x)) := by
  rw [← Φ.inner_mfderiv x, Φ.mfderiv_mgradient_comp, Φ.mfderiv_mgradient_comp]

/-- Pulling a function back along a Riemannian isometry preserves the norm of its gradient. -/
@[simp]
theorem norm_mgradient_comp (Φ : RiemannianIsometry I J M N) (u : N → ℝ) (x : M) :
    ‖mgradient I (u ∘ Φ) x‖ = ‖mgradient J u (Φ x)‖ := by
  rw [← Φ.mfderiv_mgradient_comp, Φ.norm_mfderiv]

end RiemannianIsometry

end TauCeti
