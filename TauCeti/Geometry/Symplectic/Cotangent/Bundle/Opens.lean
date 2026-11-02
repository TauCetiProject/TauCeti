/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Canonical cotangent forms on open restrictions

The canonical inclusion `T*U → T*M` over an open submanifold preserves the Liouville form
and the canonical symplectic form `ω = -dλ`. Thus the diffeomorphism
`CotangentBundle.restrictOpen` identifies the intrinsic forms of `T*U` with the restrictions
of the ambient forms to the open subset `π⁻¹(U)`. These formulas allow cotangent calculations
to be restricted to arbitrary open sets without choosing coordinates or changing signs.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 2.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

section Liouville

variable [IsManifold I 2 M]

/-- The canonical inclusion of `T*U` in `T*M` preserves the Liouville form. -/
@[simp]
theorem mpullback_openInclusion_liouvilleForm (U : Opens M) :
    SmoothForm.mpullback (openInclusion U) (contMDiff_openInclusion U) (liouvilleForm I M) =
      liouvilleForm I U := by
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.mpullback_apply, liouvilleForm_apply, liouvilleForm_apply]
  -- The commuting square of projections gives dπ_M ∘ dι = d(inclusion) ∘ dπ_U.
  have hproj : π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘
      openInclusion U = (Subtype.val : U → M) ∘
        π (E →L[ℝ] ℝ) (fun x : U ↦ TangentSpace I x →L[ℝ] ℝ) :=
    funext (proj_openInclusion U)
  have hM := mfderiv_comp_apply z
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_openInclusion U).mdifferentiableAt (by simp)) (v 0)
  have hU := mfderiv_comp_apply z
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
    ((contMDiff_proj (fun x : U ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    (v 0)
  rw [hproj, hU] at hM
  rw [← hM]
  exact openInclusion_snd_apply_mfderiv U z _

/-- The open-restriction diffeomorphism identifies the intrinsic Liouville form with the
restriction of the ambient Liouville form to `π⁻¹(U)`. -/
@[simp]
theorem mpullback_restrictOpen_liouvilleForm (U : Opens M) :
    SmoothForm.mpullback (restrictOpen U) (restrictOpen U).contMDiff
      (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (liouvilleForm I M)) = liouvilleForm I U := by
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simpa only [Function.comp_def, coe_restrictOpen] using
    mpullback_openInclusion_liouvilleForm (I := I) U

end Liouville

section Symplectic

variable [IsManifold I ∞ M]

/-- The canonical inclusion of `T*U` in `T*M` preserves the canonical symplectic form. -/
@[simp]
theorem mpullback_openInclusion_symplecticForm (U : Opens M) :
    SmoothForm.mpullback (openInclusion U) (contMDiff_openInclusion U) (symplecticForm I M) =
      symplecticForm I U := by
  rw [symplecticForm_eq_neg_mextDerivₗ, symplecticForm_eq_neg_mextDerivₗ, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_openInclusion_liouvilleForm]

/-- The open-restriction diffeomorphism identifies the intrinsic symplectic form with the
restriction of the ambient symplectic form to `π⁻¹(U)`. -/
@[simp]
theorem mpullback_restrictOpen_symplecticForm (U : Opens M) :
    SmoothForm.mpullback (restrictOpen U) (restrictOpen U).contMDiff
      (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (symplecticForm I M)) = symplecticForm I U := by
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simpa only [Function.comp_def, coe_restrictOpen] using
    mpullback_openInclusion_symplecticForm (I := I) U

end Symplectic

end TauCeti.CotangentBundle
