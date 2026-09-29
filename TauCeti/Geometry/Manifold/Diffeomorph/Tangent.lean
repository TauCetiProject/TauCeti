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
* `Diffeomorph.tangent_refl`: the tangent lift of the identity is the identity.
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K 1 P]

namespace Diffeomorph

/-- The tangent lift of a smooth diffeomorphism. Its value at `(x, v)` is
`(h x, mfderiv I J h x v)`, and its inverse is the tangent lift of `h.symm`. -/
protected def tangent (h : M ≃ₘ⟮I, J⟯ N) :
    TangentBundle I M ≃ₘ⟮I.tangent, J.tangent⟯ TangentBundle J N where
  toEquiv :=
    { toFun := tangentMap I J h
      invFun := tangentMap J I h.symm
      left_inv := tangentMap_symm_apply h (by simp)
      right_inv := tangentMap_apply_symm h (by simp) }
  contMDiff_toFun := h.contMDiff.contMDiff_tangentMap (by simp)
  contMDiff_invFun := h.symm.contMDiff.contMDiff_tangentMap (by simp)

/-- The underlying function of the tangent lift is Mathlib's `tangentMap`. -/
@[simp]
theorem coe_tangent (h : M ≃ₘ⟮I, J⟯ N) :
    ⇑h.tangent = tangentMap I J h := by
  rw [Diffeomorph.tangent]
  rfl

/-- The inverse of a tangent lift is the tangent lift of the inverse diffeomorphism. -/
@[simp]
theorem tangent_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.tangent.symm = h.symm.tangent :=
  Diffeomorph.ext fun _ ↦ rfl

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
  simpa only [coe_tangent, coe_trans, Function.comp_apply] using
    tangentMap_comp_at z ((g.mdifferentiable (by simp)) (h z.1))
      ((h.mdifferentiable (by simp)) z.1)

/-- A tangent lift carries the velocity lift of a differentiable curve to the velocity lift of
the image curve. This is the bundled tangent-map form of the chain rule. -/
theorem tangent_curveVelocityLift (h : M ≃ₘ⟮I, J⟯ N) {γ : 𝕜 → M} {t : 𝕜}
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t) :
    h.tangent (TauCeti.Manifold.curveVelocityLift I γ t) =
      TauCeti.Manifold.curveVelocityLift J (h ∘ γ) t := by
  rw [coe_tangent]
  exact TauCeti.Manifold.tangentMap_curveVelocityLift
    ((h.mdifferentiable (by simp)) (γ t)) hγ

end Diffeomorph

end
