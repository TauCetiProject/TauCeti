/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Integrability
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.Hessian.Isometry

/-!
# Conformal curvature tensors under local Riemannian isometries

A local Riemannian isometry preserves the Schouten tensor, its covariant derivative, the Weyl
tensor of type `(0,4)`, and the Cotton tensor. In particular, vanishing of Weyl or Cotton is
unchanged under passage to isometric coordinates or restriction to an open submanifold. These
identities permit the local conformal flattening equation and its integrability obstruction to
be compared on manifolds and in coordinates.

All tensors and differentials use the native tangent bundles. The source and target can have
different model spaces; equality of their dimensions follows from the invertible differential.
No global injectivity, surjectivity, orientation, or dimension bound is needed. In the exceptional
dimensions the statements respect the totalized definitions of Schouten and Weyl.

The covariant derivative of Schouten is evaluated with the derivative direction last, and the
Cotton convention is `C(u,v,w) = (∇_w P)(u,v) - (∇_v P)(u,w)`. Its transport follows from the
Schouten identity, the scalar chain rule and naturality of the Levi-Civita connection.

## Main results

In `TauCeti.IsLocalRiemannianIsometry`:

* `schoutenTensor_mfderiv`, `weylTensor_mfderiv`, `derivSchoutenTensor_mfderiv` and
  `cottonTensor_mfderiv`: evaluation of the transported tensors.
* `weylTensor_eq_zero_iff` and `cottonTensor_eq_zero_iff`: pointwise vanishing is preserved
  and reflected, even when the map is only a local isometry.
* `conformalFlatteningForm_mfderiv` and `hessian_comp_eq_conformalFlatteningForm_iff`: the
  right side and the full conformal flattening equation are natural under local isometries.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle CovariantDerivative LinearMap.BilinForm VectorField TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsLocalRiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N}

/-- A local Riemannian isometry preserves the Schouten tensor. -/
theorem schoutenTensor_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (u v : TangentSpace I x) :
    (leviCivitaConnection J N).schoutenTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).schoutenTensor x u v := by
  obtain ⟨e, -⟩ := hf.exists_linearIsometryEquiv_eq_mfderiv x
  simp only [schoutenTensor_apply, e.toLinearEquiv.finrank_eq, hf.ricciTensor_mfderiv,
    hf.scalarCurvature_map, hf.inner_mfderiv]

/-- A local Riemannian isometry preserves the Weyl tensor of type `(0,4)`. -/
theorem weylTensor_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (u v w z : TangentSpace I x) :
    (leviCivitaConnection J N).weylTensor (f x) (mfderiv I J f x u) (mfderiv I J f x v)
        (mfderiv I J f x w) (mfderiv I J f x z) =
      (leviCivitaConnection I M).weylTensor x u v w z := by
  simp only [weylTensor_apply, riemannCurvatureTensor_apply, kulkarniNomizu_apply,
    innerₗ_apply_apply, hf.inner_curvatureTensor_mfderiv, hf.schoutenTensor_mfderiv,
    hf.inner_mfderiv]

/-- A local Riemannian isometry preserves the covariant derivative of the Schouten tensor,
with the differentiating direction in the last argument. -/
@[simp]
theorem derivSchoutenTensor_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (u v w : TangentSpace I x) :
    (leviCivitaConnection J N).derivSchoutenTensor (f x) (mfderiv I J f x u)
        (mfderiv I J f x v) (mfderiv I J f x w) =
      (leviCivitaConnection I M).derivSchoutenTensor x u v w := by
  -- Extend the images of the two tensor arguments, then use the scalar chain rule on their
  -- Schouten pairing. Naturality of the connection identifies the two correction terms.
  obtain ⟨X, hX, hXu, -⟩ := hf.exists_contMDiff_mpullback_apply_eq u
  obtain ⟨Y, hY, hYv, -⟩ := hf.exists_contMDiff_mpullback_apply_eq v
  have hXd := hX.mdifferentiableAt (by simp) (x := f x)
  have hYd := hY.mdifferentiableAt (by simp) (x := f x)
  have hpair : (fun y ↦ (leviCivitaConnection I M).schoutenTensor y
      (mpullback I J f X y) (mpullback I J f Y y)) =
      (fun y ↦ (leviCivitaConnection J N).schoutenTensor y (X y) (Y y)) ∘ f := by
    funext y
    rw [← hf.schoutenTensor_mfderiv, hf.mfderiv_apply_mpullback, hf.mfderiv_apply_mpullback]
    rfl
  rw [← hXu, ← hYv, hf.mfderiv_apply_mpullback, hf.mfderiv_apply_mpullback,
    derivSchoutenTensor_apply _ hXd hYd,
    derivSchoutenTensor_apply _ (hf.mdifferentiableAt_mpullback hXd)
      (hf.mdifferentiableAt_mpullback hYd), hpair,
    mvfderiv_comp_apply x
      ((leviCivitaConnection J N).mdifferentiableAt_schoutenTensor_apply hXd hYd)
      (hf.mdifferentiableAt x)]
  simp only [← hf.mfderiv_leviCivitaConnection_mpullback hXd,
    ← hf.mfderiv_leviCivitaConnection_mpullback hYd, ← hf.mfderiv_apply_mpullback X x,
    ← hf.mfderiv_apply_mpullback Y x, hf.schoutenTensor_mfderiv]

/-- A local Riemannian isometry preserves the Cotton tensor. -/
theorem cottonTensor_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (u v w : TangentSpace I x) :
    (leviCivitaConnection J N).cottonTensor (f x) (mfderiv I J f x u)
        (mfderiv I J f x v) (mfderiv I J f x w) =
      (leviCivitaConnection I M).cottonTensor x u v w := by
  simp only [cottonTensor_apply, hf.derivSchoutenTensor_mfderiv]

/-- Vanishing of the Weyl tensor is preserved and reflected by a local Riemannian isometry. -/
theorem weylTensor_eq_zero_iff (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (leviCivitaConnection J N).weylTensor (f x) = 0 ↔
      (leviCivitaConnection I M).weylTensor x = 0 := by
  constructor
  · intro h
    ext u v w z
    rw [← hf.weylTensor_mfderiv, h]
    simp
  · intro h
    ext u v w z
    obtain ⟨u, rfl⟩ := hf.mfderiv_surjective x u
    obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x v
    obtain ⟨w, rfl⟩ := hf.mfderiv_surjective x w
    obtain ⟨z, rfl⟩ := hf.mfderiv_surjective x z
    rw [hf.weylTensor_mfderiv, h]
    simp

/-- Vanishing of the Cotton tensor is preserved and reflected by a local Riemannian isometry. -/
theorem cottonTensor_eq_zero_iff (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    (leviCivitaConnection J N).cottonTensor (f x) = 0 ↔
      (leviCivitaConnection I M).cottonTensor x = 0 := by
  constructor
  · intro h
    ext u v w
    rw [← hf.cottonTensor_mfderiv, h]
    simp
  · intro h
    ext u v w
    obtain ⟨u, rfl⟩ := hf.mfderiv_surjective x u
    obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x v
    obtain ⟨w, rfl⟩ := hf.mfderiv_surjective x w
    rw [hf.cottonTensor_mfderiv, h]
    simp

/-- The right side `P + ξ♭ ⊗ ξ♭ - |ξ|² g / 2` of the conformal flattening equation is
preserved by a local Riemannian isometry, for every value of the fibre variable `ξ`. -/
theorem conformalFlatteningForm_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M)
    (ξ u v : TangentSpace I x) :
    (leviCivitaConnection J N).conformalFlatteningForm (f x) (mfderiv I J f x ξ)
        (mfderiv I J f x u) (mfderiv I J f x v) =
      (leviCivitaConnection I M).conformalFlatteningForm x ξ u v := by
  simp only [conformalFlatteningForm_apply, ← real_inner_self_eq_norm_sq,
    hf.schoutenTensor_mfderiv, hf.inner_mfderiv]

/-- The pullback of a `C²` function solves the conformal flattening equation at `x` exactly
when the function solves it at the image point. The isometry need not be globally injective. -/
theorem hessian_comp_eq_conformalFlatteningForm_iff (hf : IsLocalRiemannianIsometry I J f)
    {φ : N → ℝ} {x : M} (hφ : ContMDiffAt J 𝓘(ℝ) 2 φ (f x)) :
    (∀ u v : TangentSpace I x, hessian I (φ ∘ f) x u v =
      (leviCivitaConnection I M).conformalFlatteningForm x (mgradient I (φ ∘ f) x) u v) ↔
    ∀ u v : TangentSpace J (f x), hessian J φ (f x) u v =
      (leviCivitaConnection J N).conformalFlatteningForm (f x) (mgradient J φ (f x)) u v := by
  have hdφ := hφ.mdifferentiableAt (by simp)
  constructor
  · intro h u v
    obtain ⟨u, rfl⟩ := hf.mfderiv_surjective x u
    obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x v
    simpa only [hf.hessian_comp hφ, ← hf.conformalFlatteningForm_mfderiv,
      hf.mfderiv_mgradient_comp hdφ] using h u v
  · intro h u v
    rw [hf.hessian_comp hφ, ← hf.conformalFlatteningForm_mfderiv,
      hf.mfderiv_mgradient_comp hdφ]
    exact h _ _

end TauCeti.IsLocalRiemannianIsometry
