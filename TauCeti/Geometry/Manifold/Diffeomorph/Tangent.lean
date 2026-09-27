/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Tangent lifts of diffeomorphisms

The differential of a smooth diffeomorphism, bundled over the map itself, is a smooth
diffeomorphism between the tangent bundles. Its inverse is the tangent lift of the inverse
diffeomorphism. This packages the tangent map in a form suitable for transporting vector fields,
integral curves, and their maximal domains.

The construction is functorial: tangent lifts preserve identity maps, inverses, and composition.
The underlying function is Mathlib's `tangentMap`; no parallel tangent-map API is introduced.

## Main definitions and results

* `Diffeomorph.tangent`: the tangent lift of a smooth diffeomorphism.
* `Diffeomorph.tangent_symm`: taking a tangent lift commutes with inversion.
* `Diffeomorph.tangent_trans`: taking a tangent lift commutes with composition.
* `Diffeomorph.tangent_curveVelocityLift`: tangent lifts carry the velocity lift of a
  differentiable curve to the velocity lift of its image.
-/

public section

open Bundle Function
open scoped ContDiff Manifold

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

namespace Diffeomorph

/-- The tangent lift of a smooth diffeomorphism. Its value at `(x, v)` is
`(h x, mfderiv I J h x v)`, and its inverse is the tangent lift of `h.symm`. -/
protected def tangent (h : M ≃ₘ⟮I, J⟯ N) :
    TangentBundle I M ≃ₘ⟮I.tangent, J.tangent⟯ TangentBundle J N where
  toEquiv :=
    { toFun := tangentMap I J h
      invFun := tangentMap J I h.symm
      left_inv := fun z ↦ by
        have hcomp := tangentMap_comp (h.symm.mdifferentiable (by simp))
          (h.mdifferentiable (by simp))
        have hinv : (h.symm : N → M) ∘ h = id := funext h.symm_apply_apply
        rw [hinv, tangentMap_id] at hcomp
        exact (congrFun hcomp z).symm
      right_inv := fun z ↦ by
        have hcomp := tangentMap_comp (h.mdifferentiable (by simp))
          (h.symm.mdifferentiable (by simp))
        have hinv : (h : M → N) ∘ h.symm = id := funext h.apply_symm_apply
        rw [hinv, tangentMap_id] at hcomp
        exact (congrFun hcomp z).symm }
  contMDiff_toFun := h.contMDiff.contMDiff_tangentMap (by simp)
  contMDiff_invFun := h.symm.contMDiff.contMDiff_tangentMap (by simp)

/-- The tangent lift is Mathlib's bundled tangent map. -/
@[simp]
theorem coe_tangent (h : M ≃ₘ⟮I, J⟯ N) :
    ⇑h.tangent = tangentMap I J h := by
  rw [Diffeomorph.tangent]
  rfl

/-- The tangent lift maps `(x, v)` to `(h x, mfderiv I J h x v)`. -/
@[simp]
theorem tangent_apply (h : M ≃ₘ⟮I, J⟯ N) (z : TangentBundle I M) :
    h.tangent z = TotalSpace.mk' F (h z.1) (mfderiv I J h z.1 z.2) := by
  rw [Diffeomorph.tangent]
  rfl

/-- The inverse of a tangent lift is the tangent lift of the inverse diffeomorphism. -/
@[simp]
theorem tangent_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.tangent.symm = h.symm.tangent := by
  apply Diffeomorph.toEquiv_injective
  rw [Diffeomorph.symm, Diffeomorph.tangent, Diffeomorph.tangent]
  rfl

/-- The tangent lift of the identity diffeomorphism is the identity diffeomorphism of the tangent
bundle. -/
@[simp]
theorem tangent_refl :
    (Diffeomorph.refl I M ∞).tangent = Diffeomorph.refl I.tangent (TangentBundle I M) ∞ := by
  apply Diffeomorph.ext
  intro z
  rw [coe_tangent, coe_refl]
  exact congrFun tangentMap_id z

/-- Tangent lift commutes with composition of smooth diffeomorphisms. -/
@[simp]
theorem tangent_trans (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P) :
    (h.trans g).tangent = h.tangent.trans g.tangent := by
  apply Diffeomorph.ext
  intro z
  have hcomp := tangentMap_comp (g.mdifferentiable (by simp)) (h.mdifferentiable (by simp))
  simpa only [coe_tangent, coe_trans, Function.comp_apply] using congrFun hcomp z

/-- A tangent lift carries the velocity lift of a differentiable curve to the velocity lift of
the image curve. This is the bundled tangent-map form of the chain rule. -/
theorem tangent_curveVelocityLift (h : M ≃ₘ⟮I, J⟯ N) {γ : 𝕜 → M} {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t) :
    h.tangent (TauCeti.Manifold.curveVelocityLift I γ t) =
      TauCeti.Manifold.curveVelocityLift J (h ∘ γ) t := by
  rw [tangent_apply, TauCeti.Manifold.curveVelocityLift_apply,
    TauCeti.Manifold.curveVelocityLift_apply]
  apply TotalSpace.ext
  · rfl
  · apply heq_of_eq
    rw [TauCeti.Manifold.curveVelocity_apply, TauCeti.Manifold.curveVelocity_apply]
    rw [mfderiv_comp t ((h.mdifferentiable (by simp)) (γ t)) hγ]
    rfl

end Diffeomorph

end
