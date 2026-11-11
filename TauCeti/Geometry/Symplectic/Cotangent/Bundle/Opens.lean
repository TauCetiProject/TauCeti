/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise

/-!
# Canonical cotangent forms on open restrictions

The canonical inclusion `T*U → T*M` over an open submanifold preserves the Liouville form
and the canonical symplectic form `ω = -dλ`. Thus the diffeomorphism
`CotangentBundle.restrictOpen` identifies the intrinsic forms of `T*U` with the restrictions
of the ambient forms to the open subset `π⁻¹(U)`. These formulas allow cotangent calculations
to be restricted to arbitrary open sets without choosing coordinates or changing signs.

The fibre translation and fibre dilation formulas of `T*M`
(`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm` and its
companions) transport along this identification to the open subset `π⁻¹(U)`, with data defined
only on `U`.

* For a one-form `β` on `U`, the fibre translation
  `TauCeti.CotangentBundle.overOpenTranslateDiffeomorph U β` of `π⁻¹(U)` sends a covector `p`
  over `x ∈ U` to `p + β_x`. It pulls the restricted Liouville form back to `λ + π^*β` and the
  restricted symplectic form back to `ω - π^*dβ`, so it is symplectic exactly when `β` is closed.
  The one-form `β` need not extend to `M`; when it is the restriction of a one-form `α` on `M`,
  the translation is the restriction of the fibre translation of `T*M` by `α`.
* For a nowhere-zero function `a` on `U`, the fibre dilation
  `TauCeti.CotangentBundle.overOpenScalarDiffeomorph U a` of `π⁻¹(U)` sends `p` over `x` to
  `a(x) • p`. For a constant `c ≠ 0` it multiplies the restricted Liouville and symplectic forms
  by `c`; when `a` is the restriction of a function on `M`, the dilation is the restriction of the
  fibre dilation of `T*M`.

Both maps are the fibre translation or dilation of `T*U`, conjugated by
`CotangentBundle.restrictOpen` through `Diffeomorph.diffCongr`. The dilation and its structural
API live with `restrictOpen` in `TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens`,
since they involve no differential forms. The translation by `0` is the identity, translations
compose by adding the one-forms, and the inverse translates by `-β`. The comparison with the
ambient maps rests on the fact that the cotangent inclusion `T*U → T*M` intertwines translations
and dilations of `T*U` by restricted data with those of `T*M`
(`TauCeti.CotangentBundle.openInclusion_vectorBundleTranslateDiffeomorph`,
`TauCeti.CotangentBundle.openInclusion_vectorBundleScalarDiffeomorph`).

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

/-! ### Fibre translation and dilation over an open subset -/

section FiberwiseLiouville

variable [IsManifold I 2 M]

/-- The inverse of the open-restriction diffeomorphism pulls the intrinsic Liouville form of
`T*U` back to the restriction of the ambient Liouville form to `π⁻¹(U)`. -/
@[simp]
theorem mpullback_restrictOpen_symm_liouvilleForm (U : Opens M) :
    SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
        (liouvilleForm I U) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (liouvilleForm I M) :=
  SmoothForm.mpullback_symm_eq_of_mpullback_eq (mpullback_restrictOpen_liouvilleForm U)

/-- The cotangent inclusion `T*U → T*M` intertwines the fibre translation of `T*U` by the
restriction to `U` of a one-form `α` on `M` with the fibre translation of `T*M` by `α`. -/
theorem openInclusion_vectorBundleTranslateDiffeomorph (U : Opens M) (α : SmoothForm I M ℝ 1)
    (z : CotangentBundle I U) :
    openInclusion U (vectorBundleTranslateDiffeomorph
        (SmoothForm.degreeOneEquiv (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α))
        (SmoothForm.degreeOneEquiv
          (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)).contMDiff z) =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff (openInclusion U z) := by
  rw [vectorBundleTranslateDiffeomorph_apply, vectorBundleTranslateDiffeomorph_apply,
    openInclusion_def, openInclusion_def]
  refine CotangentBundle.ext rfl fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  refine congrArg (_ + ·) ((SmoothForm.degreeOneEquiv_mpullback_apply _ α _ _).trans ?_)
  rw [Manifold.mfderiv_subtype_val]
  exact congrArg (SmoothForm.degreeOneEquiv α _)
    ((Manifold.tangentSpaceOpenEquiv (I := I) _).apply_symm_apply v)

/-- Conjugating a diffeomorphism `g` of `T*U` by the open-restriction diffeomorphism, the
pullback of a restricted ambient form is computed from the pullback by `g` of the corresponding
intrinsic form of `T*U`. -/
private theorem mpullback_conj_restrictOpen {k : ℕ} (U : Opens M)
    (g : CotangentBundle I U ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      CotangentBundle I U)
    (γ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ k)
    (γU : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I U) ℝ k)
    (hγ : SmoothForm.mpullback (restrictOpen U) (restrictOpen U).contMDiff
      (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val γ) = γU) :
    SmoothForm.mpullback (Diffeomorph.diffCongr (restrictOpen U) g)
        (Diffeomorph.diffCongr (restrictOpen U) g).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val γ) =
      SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
        (SmoothForm.mpullback g g.contMDiff γU) := by
  suffices ∀ φ, φ = ((restrictOpen U).symm.trans g).trans (restrictOpen U) →
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
            contMDiff_subtype_val γ) =
        SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
          (SmoothForm.mpullback g g.contMDiff γU) from
    this _ (Diffeomorph.diffCongr_apply _ _)
  rintro _ rfl
  exact (SmoothForm.mpullback_trans _ (restrictOpen U) _).trans
    ((congrArg (SmoothForm.mpullback _ _) hγ).trans (SmoothForm.mpullback_trans _ _ _))

/-- The **fibre translation of `π⁻¹(U)` by a one-form `β` on `U`**: a covector `p` of `M` over a
point `x ∈ U` is sent to `p + β_x`, where `β_x` is read as a covector of `M` through the
identification `T_x U = T_x M`. It is the fibre translation of `T*U` by `β`, transported along
the open-restriction diffeomorphism `T*U ≃ π⁻¹(U)`. The one-form `β` need not extend to `M`. -/
def overOpenTranslateDiffeomorph (U : Opens M) (β : SmoothForm I U ℝ 1) :
    overOpen (I := I) U ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      overOpen (I := I) U :=
  Diffeomorph.diffCongr (restrictOpen U) (vectorBundleTranslateDiffeomorph
    (SmoothForm.degreeOneEquiv β) (SmoothForm.degreeOneEquiv β).contMDiff)

/-- The fibre translation of `π⁻¹(U)` is the conjugate of the fibre translation of `T*U` by the
open-restriction diffeomorphism. -/
theorem overOpenTranslateDiffeomorph_eq_diffCongr (U : Opens M) (β : SmoothForm I U ℝ 1) :
    overOpenTranslateDiffeomorph U β =
      Diffeomorph.diffCongr (restrictOpen U) (vectorBundleTranslateDiffeomorph
        (SmoothForm.degreeOneEquiv β) (SmoothForm.degreeOneEquiv β).contMDiff) :=
  (rfl)

/-- The fibre translation of `π⁻¹(U)` by `β` adds to a covector over `x ∈ U` the value `β_x`,
read as a covector of `M` through the identification `T_x U = T_x M`. -/
@[simp]
theorem coe_overOpenTranslateDiffeomorph (U : Opens M) (β : SmoothForm I U ℝ 1)
    (z : overOpen (I := I) U) :
    (overOpenTranslateDiffeomorph U β z : CotangentBundle I M) =
      TotalSpace.mk' (E →L[ℝ] ℝ) z.val.proj (z.val.2 +
        SmoothForm.degreeOneEquiv β ⟨z.val.proj, (mem_overOpen U _).1 z.property⟩ ∘L
          (Manifold.tangentSpaceOpenEquiv (I := I)
            ⟨z.val.proj, (mem_overOpen U _).1 z.property⟩).symm.toContinuousLinearMap) := by
  rw [overOpenTranslateDiffeomorph_eq_diffCongr, Diffeomorph.diffCongr_apply_apply,
    coe_restrictOpen, restrictOpen_symm_apply, vectorBundleTranslateDiffeomorph_apply,
    openInclusion_def]
  refine CotangentBundle.ext rfl fun v ↦ ?_
  simp

/-- The fibre translation of `π⁻¹(U)` covers the identity of `U`. -/
theorem proj_overOpenTranslateDiffeomorph (U : Opens M) (β : SmoothForm I U ℝ 1)
    (z : overOpen (I := I) U) :
    (overOpenTranslateDiffeomorph U β z).val.proj = z.val.proj := by
  simp

/-- Translating the fibres of `π⁻¹(U)` by the zero one-form is the identity. -/
@[simp]
theorem overOpenTranslateDiffeomorph_zero (U : Opens M) :
    overOpenTranslateDiffeomorph U (0 : SmoothForm I U ℝ 1) =
      Diffeomorph.refl (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (overOpen (I := I) U) ∞ :=
  (congrArg (Diffeomorph.diffCongr (restrictOpen U))
    (Diffeomorph.ext fun p ↦ by simp)).trans (map_one _)

/-- Successive fibre translations of `π⁻¹(U)` add the one-forms on `U`. -/
theorem overOpenTranslateDiffeomorph_trans (U : Opens M) (β β' : SmoothForm I U ℝ 1) :
    (overOpenTranslateDiffeomorph U β).trans (overOpenTranslateDiffeomorph U β') =
      overOpenTranslateDiffeomorph U (β + β') :=
  (map_mul (Diffeomorph.diffCongr (restrictOpen (I := I) U))
    (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv β')
      (SmoothForm.degreeOneEquiv β').contMDiff)
    (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv β)
      (SmoothForm.degreeOneEquiv β).contMDiff)).symm.trans
    (congrArg _ ((vectorBundleTranslateDiffeomorph_trans _ _ _ _).trans
      (Diffeomorph.ext fun p ↦ by simp)))

/-- The inverse of the fibre translation of `π⁻¹(U)` by `β` is the translation by `-β`. -/
@[simp]
theorem overOpenTranslateDiffeomorph_symm (U : Opens M) (β : SmoothForm I U ℝ 1) :
    (overOpenTranslateDiffeomorph U β).symm = overOpenTranslateDiffeomorph U (-β) :=
  (Diffeomorph.diffCongr_inv _ _).trans
    (congrArg _ ((vectorBundleTranslateDiffeomorph_symm _ _).trans
      (Diffeomorph.ext fun p ↦ by simp)))

/-- For the restriction to `U` of a one-form `α` on `M`, the fibre translation of `π⁻¹(U)` is
the restriction of the fibre translation of `T*M` by `α`. -/
theorem coe_overOpenTranslateDiffeomorph_mpullback_subtype_val (U : Opens M)
    (α : SmoothForm I M ℝ 1) (z : overOpen (I := I) U) :
    (overOpenTranslateDiffeomorph U (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        z : CotangentBundle I M) =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z := by
  rw [overOpenTranslateDiffeomorph_eq_diffCongr, Diffeomorph.diffCongr_apply_apply,
    coe_restrictOpen, openInclusion_vectorBundleTranslateDiffeomorph, ← coe_restrictOpen,
    Diffeomorph.apply_symm_apply]

/-- **Fibre translation of `π⁻¹(U)` shifts the Liouville form.** Translating the fibres over an
open subset `U` by a one-form `β` on `U` pulls the restricted Liouville form back to itself plus
the pullback of `β` along the projection `π⁻¹(U) → U`. -/
theorem mpullback_overOpenTranslateDiffeomorph_liouvilleForm (U : Opens M)
    (β : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback (overOpenTranslateDiffeomorph U β)
        (overOpenTranslateDiffeomorph U β).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M) +
        SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
          (SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I U → U)
            (contMDiff_proj _) β) :=
  (mpullback_conj_restrictOpen U _ _ _ (mpullback_restrictOpen_liouvilleForm U)).trans <|
    (congrArg _ (mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm β)).trans <|
      (map_add _ _ _).trans (congrArg (· + _) (mpullback_restrictOpen_symm_liouvilleForm U))

/-- **Fibre dilation of `π⁻¹(U)` rescales the Liouville form.** Multiplying the fibres over an
open subset `U` by a nonzero real number `c` pulls the restricted Liouville form back to `c` times
itself. -/
theorem mpullback_overOpenScalarDiffeomorph_liouvilleForm (U : Opens M) {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback (overOpenScalarDiffeomorph U (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        (overOpenScalarDiffeomorph U (fun _ ↦ c) contMDiff_const fun _ ↦ hc).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M)) =
      c • SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M) := by
  rw [overOpenScalarDiffeomorph_eq_diffCongr]
  exact (mpullback_conj_restrictOpen U _ _ _ (mpullback_restrictOpen_liouvilleForm U)).trans <|
    (congrArg _ (mpullback_vectorBundleScalarDiffeomorph_liouvilleForm hc)).trans <|
      (map_smul _ _ _).trans (congrArg (c • ·) (mpullback_restrictOpen_symm_liouvilleForm U))

end FiberwiseLiouville

section FiberwiseSymplectic

variable [IsManifold I ∞ M]

/-- The inverse of the open-restriction diffeomorphism pulls the intrinsic symplectic form of
`T*U` back to the restriction of the ambient symplectic form to `π⁻¹(U)`. -/
@[simp]
theorem mpullback_restrictOpen_symm_symplecticForm (U : Opens M) :
    SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
        (symplecticForm I U) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (symplecticForm I M) :=
  SmoothForm.mpullback_symm_eq_of_mpullback_eq (mpullback_restrictOpen_symplecticForm U)

/-- **Fibre translation of `π⁻¹(U)` shifts the canonical symplectic form.** Translating the
fibres over an open subset `U` by a one-form `β` on `U` pulls the restricted symplectic form back
to itself minus the pullback of `dβ` along the projection `π⁻¹(U) → U`. -/
theorem mpullback_overOpenTranslateDiffeomorph_symplecticForm (U : Opens M)
    (β : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback (overOpenTranslateDiffeomorph U β)
        (overOpenTranslateDiffeomorph U β).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M) -
        SmoothForm.mpullback (restrictOpen U).symm (restrictOpen U).symm.contMDiff
          (SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I U → U)
            (contMDiff_proj _) (mextDerivₗ I 1 β)) :=
  (mpullback_conj_restrictOpen U _ _ _ (mpullback_restrictOpen_symplecticForm U)).trans <|
    (congrArg _ (mpullback_vectorBundleTranslateDiffeomorph_symplecticForm β)).trans <|
      (map_sub _ _ _).trans (congrArg (· - _) (mpullback_restrictOpen_symm_symplecticForm U))

/-- **Fibre translation of `π⁻¹(U)` by a closed one-form is symplectic.** Translating the fibres
over an open subset `U` by a one-form `β` on `U` preserves the restricted symplectic form exactly
when `β` is closed. -/
theorem mpullback_overOpenTranslateDiffeomorph_symplecticForm_eq_self_iff (U : Opens M)
    (β : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback (overOpenTranslateDiffeomorph U β)
        (overOpenTranslateDiffeomorph U β).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M) ↔ β.IsClosed := by
  have hinj : Function.Injective (SmoothForm.mpullback (F := ℝ) (k := 2)
      (restrictOpen (I := I) U).symm (restrictOpen U).symm.contMDiff) :=
    SmoothForm.mpullback_injective_of_rightInverse _ (restrictOpen U).contMDiff
      (restrictOpen U).symm_apply_apply
  rw [overOpenTranslateDiffeomorph_eq_diffCongr,
    mpullback_conj_restrictOpen U _ _ _ (mpullback_restrictOpen_symplecticForm U),
    ← mpullback_restrictOpen_symm_symplecticForm U, hinj.eq_iff]
  exact mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff β

/-- **Fibre dilation of `π⁻¹(U)` rescales the canonical symplectic form.** Multiplying the fibres
over an open subset `U` by a nonzero real number `c` pulls the restricted symplectic form back to
`c` times itself. -/
theorem mpullback_overOpenScalarDiffeomorph_symplecticForm (U : Opens M) {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback (overOpenScalarDiffeomorph U (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        (overOpenScalarDiffeomorph U (fun _ ↦ c) contMDiff_const fun _ ↦ hc).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      c • SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M) := by
  rw [overOpenScalarDiffeomorph_eq_diffCongr]
  exact (mpullback_conj_restrictOpen U _ _ _ (mpullback_restrictOpen_symplecticForm U)).trans <|
    (congrArg _ (mpullback_vectorBundleScalarDiffeomorph_symplecticForm hc)).trans <|
      (map_smul _ _ _).trans (congrArg (c • ·) (mpullback_restrictOpen_symm_symplecticForm U))

end FiberwiseSymplectic

end TauCeti.CotangentBundle
