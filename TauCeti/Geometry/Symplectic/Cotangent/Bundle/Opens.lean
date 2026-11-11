/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Fiberwise
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Canonical cotangent forms on open restrictions

The canonical inclusion `T*U → T*M` over an open submanifold preserves the Liouville form
and the canonical symplectic form `ω = -dλ`. Thus the diffeomorphism
`CotangentBundle.restrictOpen` identifies the intrinsic forms of `T*U` with the restrictions
of the ambient forms to the open subset `π⁻¹(U)`. These formulas allow cotangent calculations
to be restricted to arbitrary open sets without choosing coordinates or changing signs.

Transporting the fibrewise maps of `T*U` along this identification gives fibrewise maps of the
open subset `π⁻¹(U)` of `T*M`:

* the **fibre translation over `U`** by a smooth one-form `α` defined only on `U`,
  `TauCeti.CotangentBundle.overOpenTranslateDiffeomorph U α`, which adds `α_x` to a covector over
  `x ∈ U`;
* the **fibre dilation over `U`** by a nonzero real number `c`,
  `TauCeti.CotangentBundle.overOpenScalarDiffeomorph U hc`, which multiplies covectors by `c`.

When `α` is the restriction of a one-form on `M`, the first is the restriction to `π⁻¹(U)` of the
global fibre translation; the second is always the restriction of the global fibre dilation.
Write `λ_U` and `ω_U` for the restrictions of the Liouville form and of the canonical symplectic
form of `T*M` to `π⁻¹(U)`, and `π_U : π⁻¹(U) → U` for the projection. The formulas of the global
maps hold over `U`: the translation by `α` pulls `λ_U` back to `λ_U + π_U^*α` and `ω_U` back to
`ω_U - π_U^*dα`, so it preserves `ω_U` exactly when `α` is closed, and the dilation by `c`
multiplies both `λ_U` and `ω_U` by `c`. In particular a closed one-form on an open set, such as
the differential of a function defined only there, gives a symplectomorphism of the open subset
`π⁻¹(U)` of `T*M`.

## Main declarations

* `TauCeti.CotangentBundle.mpullback_restrictOpen_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_restrictOpen_symplecticForm`: the open-restriction
  diffeomorphism identifies the canonical forms.
* `TauCeti.CotangentBundle.overOpenTranslateDiffeomorph`,
  `TauCeti.CotangentBundle.overOpenScalarDiffeomorph`: fibre translation and dilation over an
  open set.
* `TauCeti.CotangentBundle.coe_overOpenTranslateDiffeomorph_mpullback_subtypeVal`,
  `TauCeti.CotangentBundle.coe_overOpenScalarDiffeomorph`: they restrict the global fibre
  translation and dilation of `T*M`.
* `TauCeti.CotangentBundle.mpullback_overOpenTranslateDiffeomorph_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_overOpenTranslateDiffeomorph_symplecticForm`,
  `TauCeti.CotangentBundle.mpullback_overOpenTranslateDiffeomorph_symplecticForm_eq_self_iff`:
  the translation formulas over an open set.
* `TauCeti.CotangentBundle.mpullback_overOpenScalarDiffeomorph_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_overOpenScalarDiffeomorph_symplecticForm`: the dilation
  formulas over an open set.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 2.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

/-! ### Conjugation of pullback identities by a diffeomorphism -/

namespace TauCeti.SmoothForm

variable {EA HA A EB HB B EC HC C G : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA] [TopologicalSpace HA] {IA : ModelWithCorners ℝ EA HA}
  [TopologicalSpace A] [ChartedSpace HA A] [IsManifold IA 1 A]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB 1 B]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC] {IC : ModelWithCorners ℝ EC HC}
  [TopologicalSpace C] [ChartedSpace HC C] [IsManifold IC 1 C]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}
  {R : A ≃ₘ⟮IA, IB⟯ B} {τ : A ≃ₘ⟮IA, IA⟯ A} {α : SmoothForm IA A G k} {β : SmoothForm IB B G k}

-- The open-restriction formulas for the cotangent bundle are instances of these four transport
-- statements. Each is applied there as a single term: rewriting step by step with the forms of an
-- open subset of the cotangent bundle is expensive to elaborate.

/-- If `R` pulls `β` back to `α`, an identity `τ^*α = c • α` transports to the conjugate of `τ` by
`R`. -/
private theorem mpullback_symm_trans_trans_eq_smul (c : ℝ) (hR : mpullback R R.contMDiff β = α)
    (hτ : mpullback τ τ.contMDiff α = c • α) :
    mpullback (R.symm.trans (τ.trans R)) (R.symm.trans (τ.trans R)).contMDiff β = c • β := by
  rw [mpullback_trans, mpullback_trans, hR, hτ, map_smul, mpullback_symm_eq_of_mpullback_eq hR]

/-- If `R` pulls `β` back to `α`, an identity `τ^*α = α + g^*δ` transports to the conjugate of `τ`
by `R`. -/
private theorem mpullback_symm_trans_trans_eq_add {g : A → C} (hg : ContMDiff IA IC ∞ g)
    {δ : SmoothForm IC C G k} (hR : mpullback R R.contMDiff β = α)
    (hτ : mpullback τ τ.contMDiff α = α + mpullback g hg δ) :
    mpullback (R.symm.trans (τ.trans R)) (R.symm.trans (τ.trans R)).contMDiff β =
      β + mpullback (g ∘ R.symm) (hg.comp R.symm.contMDiff) δ := by
  rw [mpullback_trans, mpullback_trans, hR, hτ, map_add, mpullback_symm_eq_of_mpullback_eq hR,
    mpullback_mpullback]

/-- If `R` pulls `β` back to `α`, an identity `τ^*α = α - g^*δ` transports to the conjugate of `τ`
by `R`. -/
private theorem mpullback_symm_trans_trans_eq_sub {g : A → C} (hg : ContMDiff IA IC ∞ g)
    {δ : SmoothForm IC C G k} (hR : mpullback R R.contMDiff β = α)
    (hτ : mpullback τ τ.contMDiff α = α - mpullback g hg δ) :
    mpullback (R.symm.trans (τ.trans R)) (R.symm.trans (τ.trans R)).contMDiff β =
      β - mpullback (g ∘ R.symm) (hg.comp R.symm.contMDiff) δ := by
  rw [mpullback_trans, mpullback_trans, hR, hτ, map_sub, mpullback_symm_eq_of_mpullback_eq hR,
    mpullback_mpullback]

/-- If `R` pulls `β` back to `α`, the conjugate of `τ` by `R` preserves `β` exactly when `τ`
preserves `α`. -/
private theorem mpullback_symm_trans_trans_eq_self_iff (hR : mpullback R R.contMDiff β = α) :
    mpullback (R.symm.trans (τ.trans R)) (R.symm.trans (τ.trans R)).contMDiff β = β ↔
      mpullback τ τ.contMDiff α = α := by
  rw [mpullback_trans, mpullback_trans, hR, ← mpullback_symm_eq_of_mpullback_eq hR]
  exact (mpullback_injective_of_rightInverse R.symm.contMDiff R.contMDiff
    R.symm_apply_apply).eq_iff

end TauCeti.SmoothForm

namespace TauCeti.CotangentBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-! ### Fibre translation and dilation over an open set -/

section Maps

variable [IsManifold I 1 M]

/-- The **fibre translation over an open set** `U` by a smooth one-form `α` on `U`: the
diffeomorphism of the open subset `π⁻¹(U)` of `T*M` adding `α_x` to each covector over `x ∈ U`.
It is the translation of the fibres of `T*U` by `α`, transported along
`TauCeti.CotangentBundle.restrictOpen`. -/
def overOpenTranslateDiffeomorph (U : Opens M) (α : SmoothForm I U ℝ 1) :
    overOpen (I := I) U ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      overOpen (I := I) U :=
  (restrictOpen U).symm.trans
    ((vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
      (SmoothForm.degreeOneEquiv α).contMDiff).trans (restrictOpen U))

/-- The fibre translation over an open set by `α` is the translation of `T*U` by `α`, read through
the open-restriction diffeomorphism. -/
theorem overOpenTranslateDiffeomorph_apply (U : Opens M) (α : SmoothForm I U ℝ 1)
    (z : overOpen (I := I) U) :
    overOpenTranslateDiffeomorph U α z =
      restrictOpen U (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff ((restrictOpen U).symm z)) :=
  (rfl)

/-- The fibre translation over an open set covers the identity of the base. -/
@[simp]
theorem proj_overOpenTranslateDiffeomorph (U : Opens M) (α : SmoothForm I U ℝ 1)
    (z : overOpen (I := I) U) :
    (overOpenTranslateDiffeomorph U α z).val.proj = z.val.proj := by
  simp [overOpenTranslateDiffeomorph_apply]

/-- The cotangent inclusion of an open set intertwines the fibre translation of `T*U` by the
restriction of a one-form `α` on `M` with the fibre translation of `T*M` by `α`. -/
theorem openInclusion_vectorBundleTranslateDiffeomorph_mpullback_subtypeVal (U : Opens M)
    (α : SmoothForm I M ℝ 1) (w : CotangentBundle I U) :
    openInclusion U (vectorBundleTranslateDiffeomorph
        (SmoothForm.degreeOneEquiv (SmoothForm.mpullback (Subtype.val : U → M)
          contMDiff_subtype_val α))
        (SmoothForm.degreeOneEquiv (SmoothForm.mpullback (Subtype.val : U → M)
          contMDiff_subtype_val α)).contMDiff w) =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff (openInclusion U w) := by
  -- On the fibre over `x ∈ U`, the restricted form read in `T_x M` is the form itself.
  have h : SmoothForm.degreeOneEquiv
      (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val α) w.proj ∘L
        (Manifold.tangentSpaceOpenEquiv (I := I) w.proj).symm.toContinuousLinearMap =
      SmoothForm.degreeOneEquiv α (w.proj : M) := by
    ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      SmoothForm.degreeOneEquiv_apply_apply, SmoothForm.degreeOneEquiv_apply_apply,
      SmoothForm.mpullback_apply, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [vectorBundleTranslateDiffeomorph_apply, openInclusion_def, openInclusion_def,
    vectorBundleTranslateDiffeomorph_apply, ContinuousLinearMap.add_comp, h]

/-- Over an open set `U`, the fibre translation by the restriction of a one-form `α` on `M` is the
restriction to `π⁻¹(U)` of the fibre translation of `T*M` by `α`. -/
@[simp]
theorem coe_overOpenTranslateDiffeomorph_mpullback_subtypeVal (U : Opens M)
    (α : SmoothForm I M ℝ 1) (z : overOpen (I := I) U) :
    (overOpenTranslateDiffeomorph U
        (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val α) z).val =
      vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
        (SmoothForm.degreeOneEquiv α).contMDiff z.val := by
  rw [overOpenTranslateDiffeomorph_apply, coe_restrictOpen,
    openInclusion_vectorBundleTranslateDiffeomorph_mpullback_subtypeVal, ← coe_restrictOpen,
    Diffeomorph.apply_symm_apply]

/-- The fibre dilation over an open set `U` by a nonzero real number `c`: the diffeomorphism of the
open subset `π⁻¹(U)` of `T*M` multiplying each covector by `c`. It is the dilation of the fibres
of `T*U` by `c`, transported along `TauCeti.CotangentBundle.restrictOpen`. -/
def overOpenScalarDiffeomorph (U : Opens M) {c : ℝ} (hc : c ≠ 0) :
    overOpen (I := I) U ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯
      overOpen (I := I) U :=
  (restrictOpen U).symm.trans
    ((vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
      (V := fun x : U ↦ TangentSpace I x →L[ℝ] ℝ)
      (fun _ ↦ c) (contMDiff_const (n := ∞)) fun _ ↦ hc).trans (restrictOpen U))

/-- The fibre dilation over an open set by `c` is the dilation of `T*U` by `c`, read through the
open-restriction diffeomorphism. -/
theorem overOpenScalarDiffeomorph_apply (U : Opens M) {c : ℝ} (hc : c ≠ 0)
    (z : overOpen (I := I) U) :
    overOpenScalarDiffeomorph U hc z =
      restrictOpen U (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
        (V := fun x : U ↦ TangentSpace I x →L[ℝ] ℝ)
        (fun _ ↦ c) (contMDiff_const (n := ∞)) (fun _ ↦ hc) ((restrictOpen U).symm z)) :=
  (rfl)

/-- The cotangent inclusion of an open set intertwines the fibre dilations of `T*U` and `T*M` by a
nonzero real number. -/
theorem openInclusion_vectorBundleScalarDiffeomorph (U : Opens M) {c : ℝ} (hc : c ≠ 0)
    (w : CotangentBundle I U) :
    openInclusion U (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
        (V := fun x : U ↦ TangentSpace I x →L[ℝ] ℝ)
        (fun _ ↦ c) (contMDiff_const (n := ∞)) (fun _ ↦ hc) w) =
      vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
        (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
        (fun _ ↦ c) (contMDiff_const (n := ∞)) (fun _ ↦ hc) (openInclusion U w) := by
  rw [vectorBundleScalarDiffeomorph_apply, openInclusion_def, openInclusion_def,
    vectorBundleScalarDiffeomorph_apply, ContinuousLinearMap.smul_comp]

/-- The fibre dilation over an open set `U` is the restriction to `π⁻¹(U)` of the fibre dilation
of `T*M`. -/
@[simp]
theorem coe_overOpenScalarDiffeomorph (U : Opens M) {c : ℝ} (hc : c ≠ 0)
    (z : overOpen (I := I) U) :
    (overOpenScalarDiffeomorph U hc z).val =
      vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
        (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
        (fun _ ↦ c) (contMDiff_const (n := ∞)) (fun _ ↦ hc) z.val := by
  rw [overOpenScalarDiffeomorph_apply, coe_restrictOpen,
    openInclusion_vectorBundleScalarDiffeomorph, ← coe_restrictOpen, Diffeomorph.apply_symm_apply]

end Maps

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

/-- **Fibre translation over an open set shifts the Liouville form.** Translating the covectors
over `U` by a one-form `α` on `U` pulls the restriction `λ_U` of the Liouville form to `π⁻¹(U)`
back to `λ_U + π_U^*α`. -/
theorem mpullback_overOpenTranslateDiffeomorph_liouvilleForm (U : Opens M)
    (α : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback _ (overOpenTranslateDiffeomorph U α).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M) +
        SmoothForm.mpullback (TotalSpace.proj ∘ (restrictOpen (I := I) U).symm)
          ((contMDiff_proj _).comp (restrictOpen U).symm.contMDiff) α :=
  SmoothForm.mpullback_symm_trans_trans_eq_add _ (mpullback_restrictOpen_liouvilleForm U)
    (mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm α)

/-- **Fibre dilation over an open set rescales the Liouville form.** Multiplying the covectors
over `U` by a nonzero real number `c` pulls the restriction `λ_U` of the Liouville form to
`π⁻¹(U)` back to `c • λ_U`. -/
theorem mpullback_overOpenScalarDiffeomorph_liouvilleForm (U : Opens M) {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback _ (overOpenScalarDiffeomorph U hc).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M)) =
      c • SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (liouvilleForm I M) :=
  SmoothForm.mpullback_symm_trans_trans_eq_smul c (mpullback_restrictOpen_liouvilleForm U)
    (mpullback_vectorBundleScalarDiffeomorph_liouvilleForm hc)

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

/-- **Fibre translation over an open set shifts the canonical symplectic form.** Translating the
covectors over `U` by a one-form `α` on `U` pulls the restriction `ω_U` of the canonical
symplectic form to `π⁻¹(U)` back to `ω_U - π_U^*dα`. -/
theorem mpullback_overOpenTranslateDiffeomorph_symplecticForm (U : Opens M)
    (α : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback _ (overOpenTranslateDiffeomorph U α).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M) -
        SmoothForm.mpullback (TotalSpace.proj ∘ (restrictOpen (I := I) U).symm)
          ((contMDiff_proj _).comp (restrictOpen U).symm.contMDiff) (mextDerivₗ I 1 α) :=
  SmoothForm.mpullback_symm_trans_trans_eq_sub _ (mpullback_restrictOpen_symplecticForm U)
    (mpullback_vectorBundleTranslateDiffeomorph_symplecticForm α)

/-- **Fibre translation over an open set by a closed one-form is symplectic.** Translating the
covectors over `U` by a one-form `α` on `U` preserves the restriction of the canonical symplectic
form to `π⁻¹(U)` exactly when `α` is closed. -/
theorem mpullback_overOpenTranslateDiffeomorph_symplecticForm_eq_self_iff (U : Opens M)
    (α : SmoothForm I U ℝ 1) :
    SmoothForm.mpullback _ (overOpenTranslateDiffeomorph U α).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (symplecticForm I M) ↔ α.IsClosed :=
  (SmoothForm.mpullback_symm_trans_trans_eq_self_iff
    (mpullback_restrictOpen_symplecticForm U)).trans
    (mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff α)

/-- **Fibre dilation over an open set rescales the canonical symplectic form.** Multiplying the
covectors over `U` by a nonzero real number `c` pulls the restriction `ω_U` of the canonical
symplectic form to `π⁻¹(U)` back to `c • ω_U`. -/
theorem mpullback_overOpenScalarDiffeomorph_symplecticForm (U : Opens M) {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback _ (overOpenScalarDiffeomorph U hc).contMDiff
        (SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      c • SmoothForm.mpullback (Subtype.val : overOpen (I := I) U → CotangentBundle I M)
        contMDiff_subtype_val (symplecticForm I M) :=
  SmoothForm.mpullback_symm_trans_trans_eq_smul c (mpullback_restrictOpen_symplecticForm U)
    (mpullback_vectorBundleScalarDiffeomorph_symplecticForm hc)

end Symplectic

end TauCeti.CotangentBundle
