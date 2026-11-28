/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.StrictTransform.Basic

/-!
# Composition, closed immersions and flat uniqueness of strict transforms

Let `f : X ⟶ S`, `φ : S' ⟶ S` and `U ⊆ S` open, and let `strictTransform f φ U` be the ideal sheaf
on `X ×_S S'` of the scheme-theoretic closure of the open `V = X ×_S φ⁻¹(U)`
(`Modification/StrictTransform/Basic.lean`). This file proves three structural properties of
it. None of them assumes `j : V ⟶ X ×_S S'` to be quasi-compact; the flat uniqueness results
assume instead that the inclusion `φ⁻¹(U) ⟶ S'` is quasi-compact.

* **Transitivity.** For a second morphism `ψ : S'' ⟶ S'`, write `Z' ⊆ X ×_S S'` for the strict
  transform of `f` along `φ`, viewed as a scheme over `S'`. The strict transform of `Z' ⟶ S'`
  along `ψ` with respect to `φ⁻¹(U)`, pushed into `X ×_S S''` along the canonical morphism
  `Z' ×_{S'} S'' ⟶ X ×_S S''` (`strictTransformCompHom`), is the strict transform of `f` along
  `ψ ≫ φ` with respect to `U` (`strictTransform_comp`): strict transforms along composites of
  modifications are computed in stages, the second stage with respect to `φ⁻¹(U)`.
* **Closed immersions.** If `φ` is an isomorphism over `U`, the image of the strict transform
  in `S'` is the scheme-theoretic closure of `f⁻¹(U)` mapped to `S'` through `U ≅ φ⁻¹(U)`
  (`map_snd_strictTransform`). For `f` a closed immersion, so that `X ×_S S' ⟶ S'` is one, the
  strict transform is the inverse image of that closure: it is the closure of `X ∩ U` in `S'`
  (`strictTransform_closedImmersion`). For the blowup along an ideal sheaf `I` with `U` the
  complement of its centre, the image of the strict transform in `Bl_I S` is the
  scheme-theoretic image of the morphism of blowups `Bl_{I.comap f} X ⟶ Bl_I S`
  (`map_snd_strictTransform_blowupToBase`); for `f` a closed immersion it is the blowup of `X`
  along `X ∩ V(I)` (`strictTransform_closedImmersion_blowupToBase`).
* **Uniqueness of flat closed subschemes.** If `φ⁻¹(U)` is scheme-theoretically dense in `S'`
  and its inclusion is quasi-compact, a closed subscheme `Z ⊆ X ×_S S'` which is flat over `S'`
  and agrees with `X ×_S S'` over `φ⁻¹(U)` *as closed subschemes* (its ideal sheaf pulls back to
  `⊥` on `V`) is the strict transform (`strictTransform_unique_of_flat`). The density hypothesis
  holds when `S'` is reduced, for instance integral, and `φ⁻¹(U)` is topologically dense, as for
  a modification witness (`strictTransform_unique_of_flat_of_dense`); the quasi-compactness of
  the inclusion is still assumed there, also for integral `S'`. Agreement of supports
  alone does not suffice: for `X = Spec k[ε]/(ε²)` over `S = S' = Spec k` with `φ` the identity,
  both `X` and its reduced point are flat over `S'` with the same support, and only `X` is the
  strict transform.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.strictTransformCompHom f φ U ψ`: the canonical closed
  immersion `Z' ×_{S'} S'' ⟶ X ×_S S''`, for `Z'` the strict transform of `f` along `φ`
  (`isClosedImmersion_strictTransformCompHom`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.strictTransform_comp`: transitivity of strict transforms.
* `AlgebraicGeometry.Scheme.Hom.map_snd_strictTransform` and
  `AlgebraicGeometry.Scheme.Hom.strictTransform_closedImmersion`: the strict transform as the
  closure of `X ∩ U` in `S'`.
* `AlgebraicGeometry.Scheme.Hom.map_snd_strictTransform_blowupToBase` and
  `AlgebraicGeometry.Scheme.Hom.strictTransform_closedImmersion_blowupToBase`: along a blowup, the
  strict transform of a closed subscheme is its blowup along the inverse image of the centre.
* `AlgebraicGeometry.Scheme.Hom.strictTransform_unique_of_flat` and
  `AlgebraicGeometry.Scheme.Hom.strictTransform_unique_of_flat_of_dense`: a flat closed
  subscheme agreeing with `X ×_S S'` over `φ⁻¹(U)` is the strict transform.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X S S' S'' : Scheme.{u}}

variable (f : X ⟶ S) (φ : S' ⟶ S) (U : S.Opens)

section ClosedImmersion

/-- **The image of the strict transform in `S'`.** If `φ` is an isomorphism over `U`, pushing the
strict transform forward along `X ×_S S' ⟶ S'` gives the scheme-theoretic closure in `S'` of
`f⁻¹(U)`, mapped to `S'` through `f⁻¹(U) ⟶ U ≅ φ⁻¹(U)`. -/
theorem map_snd_strictTransform (hU : IsIso (φ ∣_ U)) :
    (strictTransform f φ U).map (pullback.snd f φ) =
      (f ∣_ U ≫ inv (φ ∣_ U) ≫ (φ ⁻¹ᵁ U).ι).ker := by
  have := f.isIso_pullbackFst_morphismRestrict φ hU
  have hle : pullback.fst f φ ⁻¹ᵁ f ⁻¹ᵁ U ≤ pullback.snd f φ ⁻¹ᵁ φ ⁻¹ᵁ U := by
    rw [← comp_preimage, ← comp_preimage, pullback.condition]
  have key : (pullback.fst f φ ⁻¹ᵁ f ⁻¹ᵁ U).ι ≫ pullback.snd f φ =
      (pullback.fst f φ ∣_ (f ⁻¹ᵁ U)) ≫ f ∣_ U ≫ inv (φ ∣_ U) ≫ (φ ⁻¹ᵁ U).ι := by
    have key₂ : (pullback.snd f φ).resLE (φ ⁻¹ᵁ U) _ hle =
        (pullback.fst f φ ∣_ (f ⁻¹ᵁ U)) ≫ f ∣_ U ≫ inv (φ ∣_ U) := by
      rw [← Category.assoc, IsIso.eq_comp_inv, ← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        resLE_comp_ι_assoc, pullback.condition]
    rw [← resLE_comp_ι (pullback.snd f φ) hle, key₂]
    simp only [Category.assoc]
  rw [strictTransform_def, IdealSheafData.map_ker, strictTransformOpen_def, comp_preimage, key,
    ker_comp_of_isIso]

/-- **The strict transform of a closed subscheme.** For a closed immersion `f : X ⟶ S` and `φ` an
isomorphism over `U`, the strict transform is the inverse image in `X ×_S S'` of the
scheme-theoretic closure in `S'` of `X ∩ U`, mapped to `S'` through `U ≅ φ⁻¹(U)`. Since
`X ×_S S' ⟶ S'` is a closed immersion, the strict transform is this closure as a closed
subscheme of `S'`. -/
theorem strictTransform_closedImmersion [IsClosedImmersion f] (hU : IsIso (φ ∣_ U)) :
    strictTransform f φ U =
      (f ∣_ U ≫ inv (φ ∣_ U) ≫ (φ ⁻¹ᵁ U).ι).ker.comap (pullback.snd f φ) := by
  rw [← map_snd_strictTransform f φ U hU, IdealSheafData.comap_map_of_isClosedImmersion]

/-- **The image of the strict transform along a blowup.** For the blowup `b : Bl_I S ⟶ S` and
`U = S ∖ V(I)`, pushing the strict transform of `f : X ⟶ S` forward along
`X ×_S Bl_I S ⟶ Bl_I S` gives the ideal sheaf of the morphism of blowups
`Bl_{I.comap f} X ⟶ Bl_I S` (Stacks, Lemma 31.34.2 (080E)). For a closed immersion `f` this
morphism is a closed immersion (`IdealSheafData.isClosedImmersion_blowupMap`), so the strict
transform is the blowup of `X` along `X ∩ V(I)`, as a closed subscheme of `Bl_I S`. -/
@[stacks 080E]
theorem map_snd_strictTransform_blowupToBase (I : S.IdealSheafData) :
    (strictTransform f I.blowupToBase I.support.compl).map (pullback.snd f I.blowupToBase) =
      (I.blowupMap f).ker := by
  rw [strictTransform_blowupToBase, IdealSheafData.map_ker, IdealSheafData.blowupBaseChangeHom_snd]

/-- **The strict transform of a closed subscheme along a blowup.** For a closed immersion
`f : X ⟶ S` and the blowup `b : Bl_I S ⟶ S` with `U = S ∖ V(I)`, the strict transform is the
inverse image in `X ×_S Bl_I S` of the ideal sheaf of the closed immersion
`Bl_{I.comap f} X ⟶ Bl_I S`: as a closed subscheme of `Bl_I S`, it is the blowup of `X` along
`X ∩ V(I)` (Stacks, Lemma 31.34.2 (080E)). -/
@[stacks 080E]
theorem strictTransform_closedImmersion_blowupToBase [IsClosedImmersion f]
    (I : S.IdealSheafData) :
    strictTransform f I.blowupToBase I.support.compl =
      (I.blowupMap f).ker.comap (pullback.snd f I.blowupToBase) := by
  rw [← map_snd_strictTransform_blowupToBase, IdealSheafData.comap_map_of_isClosedImmersion]

end ClosedImmersion

section Comp

variable (ψ : S'' ⟶ S')

/-- The canonical morphism `Z' ×_{S'} S'' ⟶ X ×_S S''`, where `Z' ⊆ X ×_S S'` is the strict
transform of `f` along `φ` with respect to `U`, viewed over `S'`, and `S''` maps to `S` through
`ψ ≫ φ`. -/
def strictTransformCompHom :
    pullback ((strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ψ ⟶
      pullback f (ψ ≫ φ) :=
  pullback.lift (pullback.fst _ _ ≫ (strictTransform f φ U).subschemeι ≫ pullback.fst f φ)
    (pullback.snd _ _) (by
      simpa [pullback.condition] using pullback.condition_assoc
        (f := (strictTransform f φ U).subschemeι ≫ pullback.snd f φ) (g := ψ) φ)

@[reassoc (attr := simp)]
theorem strictTransformCompHom_fst :
    strictTransformCompHom f φ U ψ ≫ pullback.fst f (ψ ≫ φ) =
      pullback.fst _ _ ≫ (strictTransform f φ U).subschemeι ≫ pullback.fst f φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem strictTransformCompHom_snd :
    strictTransformCompHom f φ U ψ ≫ pullback.snd f (ψ ≫ φ) = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `strictTransformCompHom` is the base change of the closed immersion `Z' ⟶ X ×_S S'` along
`X ×_S S'' ⟶ X ×_S S'`, so it is a closed immersion. -/
instance isClosedImmersion_strictTransformCompHom :
    IsClosedImmersion (strictTransformCompHom f φ U ψ) := by
  have hb := IsPullback.of_hasPullback ((strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ψ
  rw [← strictTransformCompHom_snd f φ U ψ] at hb
  -- `X ×_S S''` is the base change of `X ×_S S'` along `ψ`.
  have hm : IsPullback ((pullbackLeftPullbackSndIso f φ ψ).inv ≫ pullback.fst _ _)
      (pullback.snd f (ψ ≫ φ)) (pullback.snd f φ) ψ :=
    IsPullback.of_iso_pullback ⟨by simp⟩ (pullbackLeftPullbackSndIso f φ ψ).symm rfl (by simp)
  have h : IsPullback (pullback.fst _ _) (strictTransformCompHom f φ U ψ)
      (strictTransform f φ U).subschemeι
      ((pullbackLeftPullbackSndIso f φ ψ).inv ≫ pullback.fst _ _) :=
    IsPullback.of_bot hb (pullback.hom_ext (by simp) (by simp [pullback.condition])) hm
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h inferInstance

/-- The open of `X ×_S S''` lying over `U` maps to `Z' ×_{S'} S''` over
`strictTransformCompHom`, through the closure `Z'` of the open of `X ×_S S'` lying over `U`. -/
private theorem exists_comp_strictTransformCompHom_eq :
    ∃ g : (strictTransformOpen f (ψ ≫ φ) U).toScheme ⟶
        pullback ((strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ψ,
      g ≫ strictTransformCompHom f φ U ψ = (strictTransformOpen f (ψ ≫ φ) U).ι := by
  have hm : strictTransformOpen f (ψ ≫ φ) U ≤
      ((pullbackLeftPullbackSndIso f φ ψ).inv ≫ pullback.fst _ _) ⁻¹ᵁ
        strictTransformOpen f φ U := by
    rw [strictTransformOpen_def, strictTransformOpen_def, ← comp_preimage]
    simp
  let t := ((pullbackLeftPullbackSndIso f φ ψ).inv ≫ pullback.fst _ _).resLE _ _ hm
  let a := IsClosedImmersion.lift (strictTransform f φ U).subschemeι
    (strictTransformOpen f φ U).ι
    (by rw [IdealSheafData.ker_subschemeι]; exact (strictTransform_def f φ U).le)
  have ht : t ≫ a ≫ (strictTransform f φ U).subschemeι =
      (strictTransformOpen f (ψ ≫ φ) U).ι ≫ (pullbackLeftPullbackSndIso f φ ψ).inv ≫
        pullback.fst _ _ := by
    simp [t, a, resLE_comp_ι]
  refine ⟨pullback.lift (t ≫ a) ((strictTransformOpen f (ψ ≫ φ) U).ι ≫ pullback.snd _ _) ?_, ?_⟩
  · rw [Category.assoc, reassoc_of% ht]
    simp
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, strictTransformCompHom_fst, pullback.lift_fst_assoc]
      rw [reassoc_of% ht]
      simp
    · simp

/-- **Transitivity of strict transforms.** Let `Z' ⊆ X ×_S S'` be the strict transform of `f`
along `φ` with respect to `U`, viewed over `S'`. The strict transform of `Z' ⟶ S'` along
`ψ : S'' ⟶ S'` with respect to `φ⁻¹(U)`, pushed forward to `X ×_S S''`, is the strict transform of
`f` along `ψ ≫ φ` with respect to `U`. No quasi-compactness hypothesis is needed. -/
theorem strictTransform_comp :
    (strictTransform ((strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ψ
        (φ ⁻¹ᵁ U)).map (strictTransformCompHom f φ U ψ) =
      strictTransform f (ψ ≫ φ) U := by
  -- The open over `φ⁻¹(U)` in `Z' ×_{S'} S''` is the preimage of the open over `U`.
  have hpre : strictTransformCompHom f φ U ψ ⁻¹ᵁ strictTransformOpen f (ψ ≫ φ) U =
      strictTransformOpen ((strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ψ
        (φ ⁻¹ᵁ U) := by
    have e : strictTransformCompHom f φ U ψ ≫ pullback.fst f (ψ ≫ φ) ≫ f =
        (pullback.fst _ ψ ≫ (strictTransform f φ U).subschemeι ≫ pullback.snd f φ) ≫ φ := by
      simp [pullback.condition]
    rw [strictTransformOpen_def, strictTransformOpen_def, ← comp_preimage, e, comp_preimage]
  rw [strictTransform_def (_ ≫ pullback.snd f φ) ψ, IdealSheafData.map_ker,
    strictTransform_def f (ψ ≫ φ), ← hpre]
  refine le_antisymm ?_ ((le_ker_comp
    (strictTransformCompHom f φ U ψ ∣_ strictTransformOpen f (ψ ≫ φ) U) _).trans_eq ?_)
  · obtain ⟨g, hg⟩ := exists_comp_strictTransformCompHom_eq f φ U ψ
    refine (le_ker_comp (IsOpenImmersion.lift
      (strictTransformCompHom f φ U ψ ⁻¹ᵁ strictTransformOpen f (ψ ≫ φ) U).ι g ?_) _).trans_eq ?_
    · rw [Scheme.Opens.range_ι, Set.range_subset_iff]
      intro y
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hg]
      exact y.property
    · rw [← Category.assoc, IsOpenImmersion.lift_fac, hg]
  · rw [morphismRestrict_ι]

end Comp

section Flat

open TauCeti.AlgebraicGeometry

/-- **Uniqueness of flat closed subschemes agreeing over `U`.** Let `I` be an ideal sheaf on
`X ×_S S'` whose closed subscheme `Z` is flat over `S'` and agrees with `X ×_S S'` over
`φ⁻¹(U)` as closed subschemes, that is, `I` pulls back to `⊥` on the open `X ×_S φ⁻¹(U)`. If
`φ⁻¹(U)` is scheme-theoretically dense in `S'` with quasi-compact inclusion, then `I` is the strict
transform. -/
theorem strictTransform_unique_of_flat (I : (pullback f φ).IdealSheafData)
    [QuasiCompact (φ ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (φ ⁻¹ᵁ U).ι]
    [Flat (I.subschemeι ≫ pullback.snd f φ)]
    (hI : I.comap (strictTransformOpen f φ U).ι = ⊥) : I = strictTransform f φ U := by
  set V := strictTransformOpen f φ U with hV
  set ι := I.subschemeι
  have : IsIso (pullback.fst V.ι ι) := by
    have : IsIso (I.comap V.ι).subschemeι := (isIso_subschemeι_iff_eq_bot _).mpr hI
    rw [← I.comapIso_inv_subschemeι V.ι]
    infer_instance
  have : IsIso (ι ∣_ V) := by
    rw [← (isPullback_morphismRestrict ι V).isoPullback_hom_fst]
    infer_instance
  have : IsSchemeTheoreticallyDominant (ι ⁻¹ᵁ V).ι := by
    have hW : ι ⁻¹ᵁ V = (ι ≫ pullback.snd f φ) ⁻¹ᵁ φ ⁻¹ᵁ U := by
      rw [hV, strictTransformOpen_eq_preimage_snd, comp_preimage]
    rw [hW]
    -- By flatness, the part of `Z` over `φ⁻¹(U)` is scheme-theoretically dense in `Z`.
    exact IsSchemeTheoreticallyDominant.of_isPullback
      (isPullback_morphismRestrict (ι ≫ pullback.snd f φ) (φ ⁻¹ᵁ U))
  calc I = ι.ker := I.ker_subschemeι.symm
    _ = ((ι ⁻¹ᵁ V).ι ≫ ι).ker := (ker_comp_of_isSchemeTheoreticallyDominant _ _).symm
    _ = (ι ∣_ V ≫ V.ι).ker := by rw [morphismRestrict_ι]
    _ = V.ι.ker := ker_comp_of_isIso _ _
    _ = strictTransform f φ U := (strictTransform_def f φ U).symm

/-- **Uniqueness of flat closed subschemes, for a dense preimage.** For `S'` reduced, for
instance integral, and `φ⁻¹(U)` dense in `S'` (as for a modification witness `U` of `φ`) with
quasi-compact inclusion, a closed subscheme of `X ×_S S'` flat over `S'` that agrees with
`X ×_S S'` over `φ⁻¹(U)` as closed subschemes is the strict transform. The quasi-compactness
hypothesis is not dropped for integral `S'`: it holds for instance when `S'` is noetherian. -/
theorem strictTransform_unique_of_flat_of_dense [IsReduced S'] (h : Dense (SetLike.coe (φ ⁻¹ᵁ U)))
    [QuasiCompact (φ ⁻¹ᵁ U).ι] (I : (pullback f φ).IdealSheafData)
    [Flat (I.subschemeι ≫ pullback.snd f φ)]
    (hI : I.comap (strictTransformOpen f φ U).ι = ⊥) : I = strictTransform f φ U := by
  have := AlgebraicGeometry.Opens.isDominant_ι h
  have := IsSchemeTheoreticallyDominant.of_isDominant (φ ⁻¹ᵁ U).ι
  exact strictTransform_unique_of_flat f φ U I hI

end Flat

end AlgebraicGeometry.Scheme.Hom
