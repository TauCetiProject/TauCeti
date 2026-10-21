/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.FiberwiseMap
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# Fibre translation and fibre negation of a cotangent bundle

Two diffeomorphisms of the cotangent bundle `T*M = TauCeti.CotangentBundle I M` cover the identity
of `M` and act on each fibre:

* fibre translation by a smooth one-form `α`, `p ↦ p + α_x` on the fibre over `x`
  (`TauCeti.CotangentBundle.fiberTranslation`);
* fibre negation, `p ↦ -p` (`TauCeti.CotangentBundle.fiberNeg`).

This file computes how they act on the Liouville form `λ` and on the canonical symplectic form
`ω = -dλ`. Writing `π : T*M → M` for the projection and `τ_α` for translation by `α`,

* `τ_α^* λ = λ + π^* α` (`TauCeti.CotangentBundle.mpullback_fiberTranslation_liouvilleForm`), hence
  `τ_α^* ω = ω - π^* dα` (`TauCeti.CotangentBundle.mpullback_fiberTranslation_symplecticForm`);
* consequently `τ_α` preserves `ω` exactly when `α` is closed
  (`TauCeti.CotangentBundle.mpullback_fiberTranslation_symplecticForm_eq_self_iff`): the
  pullback `π^*` is injective on forms, since `π` has the zero section as a smooth right inverse;
* fibre negation reverses the signs of both forms
  (`TauCeti.CotangentBundle.mpullback_fiberNeg_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_fiberNeg_symplecticForm`).

All of these come from one observation: pulling `λ` back along any differentiable self-map `Φ` of
`T*M` that covers the identity of `M` evaluates the image covector `Φ p` on the derivative of the
projection (`TauCeti.CotangentBundle.mpullback_liouvilleForm_apply_of_proj_eq`, the self-map case
of `TauCeti.CotangentBundle.mpullback_liouvilleForm_apply`).

As in `TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville`, the base may have boundary or
corners and need not be finite-dimensional.

## Main declarations

* `TauCeti.CotangentBundle.fiberTranslation`: translation of the fibres by a smooth one-form.
* `TauCeti.CotangentBundle.fiberNeg`: negation of the fibres.
* `TauCeti.CotangentBundle.mpullback_fiberTranslation_liouvilleForm`: `τ_α^* λ = λ + π^* α`.
* `TauCeti.CotangentBundle.mpullback_fiberTranslation_symplecticForm_eq_self_iff`: `τ_α` is
  symplectic if and only if `dα = 0`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Diffeomorph

variable [IsManifold I 1 M]

/-- **Fibre translation** of the cotangent bundle by a smooth one-form `α`: the diffeomorphism of
`T*M` sending a covector `p` over `x` to `p + α_x`. Its inverse is translation by `-α`. -/
def fiberTranslation (α : SmoothForm I M ℝ 1) :
    CotangentBundle I M ≃ₘ^∞⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      CotangentBundle I M where
  toFun z := TotalSpace.mk' (E →L[ℝ] ℝ) z.proj (z.2 + SmoothForm.degreeOneEquiv α z.proj)
  invFun z := TotalSpace.mk' (E →L[ℝ] ℝ) z.proj (z.2 + -SmoothForm.degreeOneEquiv α z.proj)
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun :=
    contMDiff_totalSpace_mk_add_section (SmoothForm.degreeOneEquiv α).contMDiff
  contMDiff_invFun :=
    contMDiff_totalSpace_mk_add_section (SmoothForm.degreeOneEquiv α).contMDiff.neg_section

/-- Fibre translation by `α` adds the covector `α_x` to a covector over `x`. -/
@[simp]
theorem fiberTranslation_apply (α : SmoothForm I M ℝ 1) (z : CotangentBundle I M) :
    fiberTranslation α z =
      TotalSpace.mk' (E →L[ℝ] ℝ) z.proj (z.2 + SmoothForm.degreeOneEquiv α z.proj) :=
  (rfl)

/-- Fibre translation covers the identity of the base. -/
theorem proj_fiberTranslation (α : SmoothForm I M ℝ 1) (z : CotangentBundle I M) :
    (fiberTranslation α z).proj = z.proj :=
  (rfl)

/-- Translation by the zero form is the identity. -/
@[simp]
theorem fiberTranslation_zero :
    fiberTranslation (0 : SmoothForm I M ℝ 1) = Diffeomorph.refl _ _ _ :=
  Diffeomorph.ext fun z ↦ by simp

/-- Translation by a sum of one-forms is the composite of the two translations. -/
theorem fiberTranslation_add (α β : SmoothForm I M ℝ 1) :
    fiberTranslation (α + β) = (fiberTranslation α).trans (fiberTranslation β) :=
  Diffeomorph.ext fun z ↦ by simp [add_assoc]

/-- The inverse of translation by `α` is translation by `-α`. -/
@[simp]
theorem fiberTranslation_symm (α : SmoothForm I M ℝ 1) :
    (fiberTranslation α).symm = fiberTranslation (-α) :=
  Diffeomorph.ext fun z ↦ (fiberTranslation α).toEquiv.symm_apply_eq.mpr (by simp)

/-- **Fibre negation** of the cotangent bundle: the involutive diffeomorphism of `T*M` sending a
covector `p` to `-p`, as fibrewise multiplication by `-1`. -/
def fiberNeg :
    CotangentBundle I M ≃ₘ^∞⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      CotangentBundle I M :=
  vectorBundleScalarDiffeomorph (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (fun _ ↦ (-1 : ℝ))
    contMDiff_const fun _ ↦ by norm_num

/-- Fibre negation negates a covector. -/
@[simp]
theorem fiberNeg_apply (z : CotangentBundle I M) :
    fiberNeg z = TotalSpace.mk' (E →L[ℝ] ℝ) z.proj (-z.2) := by
  simp [fiberNeg]

/-- Fibre negation covers the identity of the base. -/
theorem proj_fiberNeg (z : CotangentBundle I M) : (fiberNeg z).proj = z.proj := by
  rw [fiberNeg_apply]

/-- Fibre negation is an involution. -/
@[simp]
theorem fiberNeg_symm :
    (fiberNeg : CotangentBundle I M ≃ₘ^∞⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      CotangentBundle I M).symm = fiberNeg :=
  Diffeomorph.ext fun z ↦ by simp [fiberNeg]

end Diffeomorph

section Liouville

variable [IsManifold I 2 M]

/-- **Pullback of the Liouville form by a map covering the identity.** If a self-map `Φ` of `T*M`
preserves base points and is differentiable at `z`, the pullback of the Liouville form evaluates a
tangent vector `v` at `z` by applying the covector `Φ z` to the derivative of the projection. -/
theorem mpullback_liouvilleForm_apply_of_proj_eq
    {Φ : CotangentBundle I M → CotangentBundle I M} (hΦ : ∀ z, (Φ z).proj = z.proj)
    {z : CotangentBundle I M}
    (hΦz : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Φ z)
    (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    mpullback (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) Φ (liouvilleForm I M).1 z v =
      (Φ z).2 (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z (v 0)) := by
  rw [mpullback_liouvilleForm_apply hΦz]
  exact congrArg (fun g ↦ (Φ z).2 (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I g z (v 0))) (funext hΦ)

/-- **Fibre translation changes the Liouville form by the pulled-back one-form:**
`τ_α^* λ = λ + π^* α`. -/
theorem mpullback_fiberTranslation_liouvilleForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (fiberTranslation α) (fiberTranslation α).contMDiff
        (liouvilleForm I M) =
      liouvilleForm I M +
        SmoothForm.mpullback (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
          (Bundle.contMDiff_proj _) α := by
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_eq
      (proj_fiberTranslation α) ((fiberTranslation α).mdifferentiable (by simp) z),
    fiberTranslation_apply]
  simp [liouvilleForm_apply, SmoothForm.mpullback_apply_degreeOne, -SmoothForm.coe_mpullback]

/-- **Fibre negation reverses the sign of the Liouville form.** -/
theorem mpullback_fiberNeg_liouvilleForm :
    SmoothForm.mpullback fiberNeg fiberNeg.contMDiff (liouvilleForm I M) = -liouvilleForm I M := by
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_eq proj_fiberNeg
      (fiberNeg.mdifferentiable (by simp) z), fiberNeg_apply]
  simp [liouvilleForm_apply]

end Liouville

section Symplectic

variable [IsManifold I ∞ M]

/-- **Fibre translation changes the canonical symplectic form by the pulled-back derivative:**
`τ_α^* ω = ω - π^* dα`. -/
theorem mpullback_fiberTranslation_symplecticForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (fiberTranslation α) (fiberTranslation α).contMDiff
        (symplecticForm I M) =
      symplecticForm I M -
        SmoothForm.mpullback (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ))
          (Bundle.contMDiff_proj _) (mextDerivₗ I 1 α) := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_fiberTranslation_liouvilleForm]
  simp only [map_add, SmoothForm.mextDerivₗ_mpullback]
  abel

/-- **Fibre translation by `α` is symplectic exactly when `α` is closed.** -/
theorem mpullback_fiberTranslation_symplecticForm_eq_self_iff (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (fiberTranslation α) (fiberTranslation α).contMDiff
        (symplecticForm I M) = symplecticForm I M ↔ α.IsClosed := by
  -- The projection has the zero section as a smooth right inverse, so `π^*` is injective.
  have hinj := SmoothForm.mpullback_injective (F := ℝ) (k := 2)
    (Bundle.contMDiff_zeroSection ℝ (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (F := E →L[ℝ] ℝ)
      (IB := I))
    (Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) (zeroSection_proj _ _)
  rw [mpullback_fiberTranslation_symplecticForm, sub_eq_self, map_eq_zero_iff _ hinj]
  -- It remains to identify the vanishing of `dα` with closedness.
  simp only [SmoothForm.isClosed_def, ← mextDerivₗ_apply I, ZeroMemClass.coe_eq_zero]

/-- **Fibre negation reverses the sign of the canonical symplectic form.** -/
theorem mpullback_fiberNeg_symplecticForm :
    SmoothForm.mpullback fiberNeg fiberNeg.contMDiff (symplecticForm I M) =
      -symplecticForm I M := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_fiberNeg_liouvilleForm]
  simp

end Symplectic

end CotangentBundle

end TauCeti
