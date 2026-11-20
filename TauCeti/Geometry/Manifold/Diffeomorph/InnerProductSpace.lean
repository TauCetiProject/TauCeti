/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Analysis.Calculus.ContDiff.Adjoint

/-!
# The cotangent map of a diffeomorphism of inner product spaces

Identifying covectors with vectors by the inner product, the cotangent map of a diffeomorphism
`h : E → F` of complete real inner product spaces at `x` sends a covector `ξ` at `x` to the
covector `(Dh(x)ᵀ)⁻¹ ξ` at `h x`, characterized by `⟪(Dh(x)ᵀ)⁻¹ ξ, Dh(x) v⟫ = ⟪ξ, v⟫`
(`Diffeomorph.inner_adjoint_fderiv_symm_apply_fderiv_apply`). Here `(Dh(x)ᵀ)⁻¹` is the adjoint
of `D(h⁻¹)(h x)`.

The adjoint of `Dh(x)` is a two-sided inverse of the cotangent map
(`Diffeomorph.adjoint_fderiv_adjoint_fderiv_symm_apply`,
`Diffeomorph.adjoint_fderiv_symm_adjoint_fderiv_apply`), so the cotangent map sends nonzero
covectors to nonzero covectors (`Diffeomorph.adjoint_fderiv_symm_apply_ne_zero`). The cotangent
map of a composition is the composition of the cotangent maps
(`Diffeomorph.adjoint_fderiv_trans_symm`). For a `C^n` diffeomorphism the cotangent map and its
inverse depend `C^m`-smoothly on the base point for `m + 1 ≤ n`
(`Diffeomorph.contDiff_adjoint_fderiv_symm`, `Diffeomorph.contDiff_adjoint_fderiv_comp_symm`).
-/

public section

open scoped ContDiff Manifold RealInnerProductSpace

open ContinuousLinearMap

namespace Diffeomorph

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G] {n m : ℕ∞ω}

/-- The cotangent map `y ↦ D(h⁻¹)(y)ᵀ`, as a function of the image point `y`, is `C^m` for a
`C^n` diffeomorphism `h` with `m + 1 ≤ n`. -/
theorem contDiff_adjoint_fderiv_symm (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m fun y ↦ adjoint (fderiv ℝ h.symm y) :=
  (h.symm.contDiff.fderiv_right hmn).adjoint

/-- The inverse `y ↦ Dh(h⁻¹ y)ᵀ` of the cotangent map, as a function of the image point `y`, is
`C^m` for a `C^n` diffeomorphism `h` with `m + 1 ≤ n`. -/
theorem contDiff_adjoint_fderiv_comp_symm (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m fun y ↦ adjoint (fderiv ℝ h (h.symm y)) :=
  (h.contDiff_fderiv_comp_symm hmn).adjoint

/-- The adjoint of `Dh(h⁻¹ y)` is a left inverse of the adjoint of `D(h⁻¹)(y)`. -/
theorem adjoint_fderiv_comp_adjoint_fderiv_symm (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hn : n ≠ 0)
    (y : F) :
    (adjoint (fderiv ℝ h (h.symm y))).comp (adjoint (fderiv ℝ h.symm y)) =
      ContinuousLinearMap.id ℝ E := by
  have hid := h.fderiv_symm_comp_fderiv hn (h.symm y)
  rw [h.apply_symm_apply] at hid
  rw [← adjoint_comp, hid, adjoint_id]

/-- **The cotangent map preserves the pairing of covectors with tangent vectors:** the image
`(Dh(x)ᵀ)⁻¹ ξ` of `ξ`, paired with `Dh(x) v`, is `ξ` paired with `v`. -/
@[simp]
theorem inner_adjoint_fderiv_symm_apply_fderiv_apply (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F)
    (hn : n ≠ 0) (x ξ v : E) :
    ⟪adjoint (fderiv ℝ h.symm (h x)) ξ, fderiv ℝ h x v⟫ = ⟪ξ, v⟫ := by
  rw [adjoint_inner_left, ← comp_apply, h.fderiv_symm_comp_fderiv hn, id_apply]

/-- The adjoint of `Dh(x)` is a left inverse of the cotangent map at `x`. -/
@[simp]
theorem adjoint_fderiv_adjoint_fderiv_symm_apply (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hn : n ≠ 0)
    (x : E) (ξ : E) : adjoint (fderiv ℝ h x) (adjoint (fderiv ℝ h.symm (h x)) ξ) = ξ := by
  simpa using congrArg (fun A ↦ A ξ) (h.adjoint_fderiv_comp_adjoint_fderiv_symm hn (h x))

/-- The adjoint of `Dh(x)` is a right inverse of the cotangent map at `x`. -/
@[simp]
theorem adjoint_fderiv_symm_adjoint_fderiv_apply (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hn : n ≠ 0)
    (x : E) (η : F) : adjoint (fderiv ℝ h.symm (h x)) (adjoint (fderiv ℝ h x) η) = η := by
  have hid := h.fderiv_comp_fderiv_symm hn (h x)
  rw [h.symm_apply_apply] at hid
  rw [← comp_apply, ← adjoint_comp, hid, adjoint_id, id_apply]

/-- The cotangent map sends nonzero covectors to nonzero covectors: it has a left inverse. -/
theorem adjoint_fderiv_symm_apply_ne_zero (h : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (hn : n ≠ 0)
    {x ξ : E} (hξ : ξ ≠ 0) : adjoint (fderiv ℝ h.symm (h x)) ξ ≠ 0 := fun h0 ↦
  hξ (by simpa [h0] using (h.adjoint_fderiv_adjoint_fderiv_symm_apply hn x ξ).symm)

/-- The cotangent map of `h₂ ∘ h₁` at `x` is the cotangent map of `h₂` at `h₁ x` composed with
that of `h₁` at `x`. -/
theorem adjoint_fderiv_trans_symm (h₁ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F)
    (h₂ : F ≃ₘ^n⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ G) (hn : n ≠ 0) (x : E) :
    adjoint (fderiv ℝ (h₁.trans h₂).symm ((h₁.trans h₂) x)) =
      (adjoint (fderiv ℝ h₂.symm (h₂ (h₁ x)))).comp (adjoint (fderiv ℝ h₁.symm (h₁ x))) := by
  rw [symm_trans', fderiv_trans _ _ hn, adjoint_comp]
  simp

end Diffeomorph
