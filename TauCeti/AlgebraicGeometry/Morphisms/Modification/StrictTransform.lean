/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.StrictTransform
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Strict transforms along modifications

Let `φ : S' ⟶ S` be a morphism of schemes and `U ⊆ S` an open. The pair is a *modification
witness* (`IsModification.Witness φ U`) if `U` is dense, its preimage `φ⁻¹(U)` is dense in `S'`,
and `φ` restricts to an isomorphism `φ⁻¹(U) ≅ U`. A proper morphism is a modification exactly when
it has a witness (`IsModification.iff_exists_witness`), and the iso locus of a modification is the
largest witness (`IsModification.witness_isoLocus`).

For a morphism `f : X ⟶ S`, put `Y = X ×_S S'` and let `V ⊆ Y` be the open lying over `U`, that is
the open `X ×_S φ⁻¹(U)` (`strictTransformOpen f φ U`). The *strict transform* of `f` along `φ`
with respect to `U` is the ideal sheaf on `Y` of the scheme-theoretic closure of `V`, the kernel of
the open immersion `j : V ⟶ Y` (`strictTransform f φ U`). The witness is part of the data: for
a non-reduced `X` the strict transform depends on it. The definition makes sense for every `U`;
the comparison with the topological closure needs `j` quasi-compact, which holds for instance when
`Y` is locally Noetherian, when the complement of `U` is cut out by a finite-type ideal sheaf, or
in the blowup case.

## Main definitions

* `TauCeti.AlgebraicGeometry.IsModification.Witness φ U`: `U` is a dense open of `S` with dense
  preimage over which `φ` is an isomorphism.
* `TauCeti.AlgebraicGeometry.strictTransformOpen f φ U`: the open `X ×_S φ⁻¹(U)` of `X ×_S S'`.
* `TauCeti.AlgebraicGeometry.strictTransform f φ U`: the ideal sheaf of its scheme-theoretic
  closure.

## Main results

* `TauCeti.AlgebraicGeometry.strictTransform_eq_closure`: for quasi-compact `j`, the support of
  the strict transform is the closure of `V`.
* `TauCeti.AlgebraicGeometry.strictTransform_eq_of_le`: for `U ≤ U'` with `φ` an isomorphism over
  `U'` and `f⁻¹(U)` scheme-theoretically dense in `f⁻¹(U')`, the strict transforms agree;
  `strictTransform_eq_of_isSchemeTheoreticallyDominant` is the same statement with the density
  asked of the opens of `X ×_S S'`.
* `TauCeti.AlgebraicGeometry.strictTransform_top` and `strictTransform_bot`: the open `U = S` gives
  the zero ideal sheaf and `U = ∅` the unit ideal sheaf.
* `TauCeti.AlgebraicGeometry.strictTransform_id`: for `S'` reduced and `φ⁻¹(U)` dense, as for a
  modification witness, the strict transform of the identity of `S` is the zero ideal sheaf on
  `S ×_S S' ≅ S'`.
* `TauCeti.AlgebraicGeometry.strictTransform_eq_blowup`: for the blowup `Bl_I S ⟶ S` and
  `U = S ∖ V(I)`, the strict transform is the ideal sheaf of the blowup of `X` along `I.comap f`,
  embedded in `X ×_S Bl_I S`.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ): modifications.
* [Stacks Project, Definition 31.34.1](https://stacks.math.columbia.edu/tag/080D) and
  [Lemma 31.34.2](https://stacks.math.columbia.edu/tag/080E): strict transforms along blowups.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {X S S' : Scheme.{u}}

/-- A *modification witness* for `φ : S' ⟶ S` is an open `U ⊆ S` that is dense, has dense preimage
`φ⁻¹(U)` in `S'`, and over which `φ` is an isomorphism. A proper morphism with a witness is a
modification (`IsModification.of_witness`). -/
structure IsModification.Witness (φ : S' ⟶ S) (U : S.Opens) : Prop where
  /-- The open `U` is dense in `S`. -/
  dense : Dense (U : Set S)
  /-- The preimage `φ⁻¹(U)` is dense in `S'`. -/
  dense_preimage : Dense (φ ⁻¹ᵁ U : Set S')
  /-- `φ` restricts to an isomorphism `φ⁻¹(U) ≅ U`. -/
  isIso : IsIso (φ ∣_ U)

namespace IsModification

/-- Every modification has a witness. -/
theorem exists_witness (φ : S' ⟶ S) [IsModification φ] : ∃ U, Witness φ U := by
  obtain ⟨U, hU, hφU, h⟩ := exists_isIso_morphismRestrict (f := φ)
  exact ⟨U, hU, hφU, h⟩

/-- A proper morphism with a modification witness is a modification. -/
theorem of_witness (φ : S' ⟶ S) [IsProper φ] {U : S.Opens} (h : Witness φ U) :
    IsModification φ where
  exists_isIso_morphismRestrict := ⟨U, h.dense, h.dense_preimage, h.isIso⟩

/-- A proper morphism is a modification exactly when it has a witness. -/
theorem iff_exists_witness (φ : S' ⟶ S) [IsProper φ] :
    IsModification φ ↔ ∃ U, Witness φ U :=
  ⟨fun _ ↦ exists_witness φ, fun ⟨_, h⟩ ↦ of_witness φ h⟩

/-- The whole target is a witness for an isomorphism. -/
theorem witness_top (φ : S' ⟶ S) [IsIso φ] : Witness φ ⊤ :=
  ⟨by simp, by simp, inferInstance⟩

/-- A witness is contained in the iso locus. -/
theorem Witness.le_isoLocus {φ : S' ⟶ S} {U : S.Opens} (h : Witness φ U) : U ≤ φ.isoLocus :=
  φ.le_isoLocus_iff.mpr h.isIso

/-- A larger open over which `φ` is still an isomorphism is again a witness. -/
theorem Witness.mono {φ : S' ⟶ S} {U U' : S.Opens} (h : Witness φ U) (hUU' : U ≤ U')
    (hU' : IsIso (φ ∣_ U')) : Witness φ U' :=
  ⟨h.dense.mono hUU', h.dense_preimage.mono (φ.preimage_mono hUU'), hU'⟩

/-- The iso locus of a modification is a witness, the largest one (`Witness.le_isoLocus`). -/
theorem witness_isoLocus (φ : S' ⟶ S) [IsModification φ] : Witness φ φ.isoLocus := by
  obtain ⟨U, hU⟩ := exists_witness φ
  exact hU.mono hU.le_isoLocus inferInstance

end IsModification

variable (f : X ⟶ S) (φ : S' ⟶ S) (U : S.Opens)

/-- The open `V = X ×_S φ⁻¹(U)` of `X ×_S S'` lying over `U ⊆ S`, written as the preimage of `U`
under `X ×_S S' ⟶ X ⟶ S`. -/
def strictTransformOpen : (pullback f φ).Opens :=
  (pullback.fst f φ ≫ f) ⁻¹ᵁ U

/-- The open lying over `U` is the preimage of `U` under the projection to `X` followed by `f`. -/
theorem strictTransformOpen_def :
    strictTransformOpen f φ U = (pullback.fst f φ ≫ f) ⁻¹ᵁ U :=
  (rfl)

/-- The open lying over `U` is also the preimage of `φ⁻¹(U)` under the projection to `S'`. -/
theorem strictTransformOpen_eq_preimage_snd :
    strictTransformOpen f φ U = pullback.snd f φ ⁻¹ᵁ φ ⁻¹ᵁ U := by
  rw [strictTransformOpen_def, pullback.condition, Scheme.Hom.comp_preimage]

/-- Shrinking `U` shrinks the open lying over it. -/
theorem strictTransformOpen_mono {U U' : S.Opens} (h : U ≤ U') :
    strictTransformOpen f φ U ≤ strictTransformOpen f φ U' :=
  Scheme.Hom.preimage_mono _ h

/-- The *strict transform* of `f : X ⟶ S` along `φ : S' ⟶ S` with respect to the open `U ⊆ S`: the
ideal sheaf on `X ×_S S'` of the scheme-theoretic closure of the open `X ×_S φ⁻¹(U)`, that is,
the kernel of its inclusion. It is meant for a modification witness `U` of `φ`
(`IsModification.Witness`); see `strictTransform_eq_closure` for its support. -/
def strictTransform : (pullback f φ).IdealSheafData :=
  (strictTransformOpen f φ U).ι.ker

/-- The strict transform is the kernel of the inclusion of the open lying over `U`. -/
theorem strictTransform_def : strictTransform f φ U = (strictTransformOpen f φ U).ι.ker :=
  (rfl)

/-- **The strict transform is supported on the closure of the open over `U`.** When the inclusion
`j : X ×_S φ⁻¹(U) ⟶ X ×_S S'` is quasi-compact, the support of the strict transform is the
topological closure of `X ×_S φ⁻¹(U)`. -/
theorem strictTransform_eq_closure [QuasiCompact (strictTransformOpen f φ U).ι] :
    SetLike.coe (strictTransform f φ U).support =
      closure (SetLike.coe (strictTransformOpen f φ U)) := by
  rw [strictTransform_def, Scheme.Hom.support_ker, Scheme.Opens.range_ι]

/-- The open over `U` lies in the support of the strict transform, with no quasi-compactness
hypothesis. -/
theorem strictTransformOpen_subset_support :
    SetLike.coe (strictTransformOpen f φ U) ⊆ SetLike.coe (strictTransform f φ U).support := by
  rw [strictTransform_def]
  simpa using (strictTransformOpen f φ U).ι.range_subset_ker_support

/-- Opens `V ≤ V'` of a scheme with `V` scheme-theoretically dense in `V'` have the same
scheme-theoretic closure. -/
theorem _root_.AlgebraicGeometry.Scheme.Opens.ker_ι_eq_of_isSchemeTheoreticallyDominant
    {Y : Scheme.{u}} {V V' : Y.Opens} (h : V ≤ V') [IsSchemeTheoreticallyDominant (Y.homOfLE h)] :
    V.ι.ker = V'.ι.ker := by
  rw [← Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant (Y.homOfLE h) V'.ι, Scheme.homOfLE_ι]

/-- **Shrinking the witness.** If `U ≤ U'` and the open over `U` is scheme-theoretically dense in
the open over `U'`, the strict transforms with respect to `U` and `U'` agree. -/
theorem strictTransform_eq_of_isSchemeTheoreticallyDominant {U U' : S.Opens} (h : U ≤ U')
    [IsSchemeTheoreticallyDominant
      ((pullback f φ).homOfLE (strictTransformOpen_mono f φ h))] :
    strictTransform f φ U = strictTransform f φ U' :=
  Scheme.Opens.ker_ι_eq_of_isSchemeTheoreticallyDominant (strictTransformOpen_mono f φ h)

/-- If `φ` is an isomorphism over `U`, then the projection `X ×_S S' ⟶ X` is an isomorphism over
`f⁻¹(U)`: it is the base change of `φ⁻¹(U) ≅ U` along `f⁻¹(U) ⟶ U`. -/
theorem isIso_pullbackFst_morphismRestrict {U : S.Opens} (hU : IsIso (φ ∣_ U)) :
    IsIso (pullback.fst f φ ∣_ (f ⁻¹ᵁ U)) := by
  have s := (isPullback_morphismRestrict (pullback.fst f φ) (f ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback f φ).flip
  rw [← morphismRestrict_ι] at s
  exact (s.of_right' (isPullback_morphismRestrict φ U).flip).isIso_snd_of_isIso

/-- **Independence of the witness.** Let `U ≤ U'` be opens of `S` with `φ` an isomorphism over
`U'`. If `f⁻¹(U)` is scheme-theoretically dense in `f⁻¹(U')`, then the strict transforms of `f`
with respect to `U` and `U'` agree. Over `U'` the open `X ×_S φ⁻¹(U')` is `f⁻¹(U')`, so the
density transfers to the opens of `X ×_S S'`. For `X` reduced and `U`, `U'` dense witnesses the
density condition holds; for `X` with embedded components it can fail. -/
theorem strictTransform_eq_of_le {U U' : S.Opens} (h : U ≤ U') (hU' : IsIso (φ ∣_ U'))
    [IsSchemeTheoreticallyDominant (X.homOfLE (f.preimage_mono h))] :
    strictTransform f φ U = strictTransform f φ U' := by
  have hU : IsIso (φ ∣_ U) := φ.le_isoLocus_iff.mp (h.trans (φ.le_isoLocus_iff.mpr hU'))
  have := isIso_pullbackFst_morphismRestrict f φ hU
  have := isIso_pullbackFst_morphismRestrict f φ hU'
  have hle : pullback.fst f φ ⁻¹ᵁ f ⁻¹ᵁ U ≤ pullback.fst f φ ⁻¹ᵁ f ⁻¹ᵁ U' :=
    Scheme.Hom.preimage_mono _ (f.preimage_mono h)
  have key : (pullback f φ).homOfLE hle =
      pullback.fst f φ ∣_ (f ⁻¹ᵁ U) ≫ X.homOfLE (f.preimage_mono h) ≫
        inv (pullback.fst f φ ∣_ (f ⁻¹ᵁ U')) := by
    rw [← Category.assoc, IsIso.eq_comp_inv, ← cancel_mono (f ⁻¹ᵁ U').ι]
    simp
  have : IsSchemeTheoreticallyDominant ((pullback f φ).homOfLE hle) := by
    rw [key]
    infer_instance
  rw [strictTransform_def, strictTransform_def, strictTransformOpen_def, strictTransformOpen_def,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  exact Scheme.Opens.ker_ι_eq_of_isSchemeTheoreticallyDominant hle

/-- For `U = S` the strict transform is the zero ideal sheaf: nothing is removed. -/
@[simp]
theorem strictTransform_top : strictTransform f φ ⊤ = ⊥ := by
  have : strictTransformOpen f φ ⊤ = ⊤ := by simp [strictTransformOpen_def]
  rw [strictTransform_def, this, ← Scheme.topIso_hom]
  exact Scheme.Hom.ker_eq_bot_of_isIso _

/-- For `U = ∅` the strict transform is the unit ideal sheaf: it cuts out the empty subscheme. -/
@[simp]
theorem strictTransform_bot : strictTransform f φ ⊥ = ⊤ := by
  have : strictTransformOpen f φ ⊥ = ⊥ := by simp [strictTransformOpen_def]
  rw [strictTransform_def, Scheme.Hom.ker_eq_top_iff_isEmpty, this]
  exact ⟨fun x ↦ by simpa using x.property⟩

/-- **The strict transform of the identity.** For `S'` reduced, for instance integral, and `φ⁻¹(U)`
dense in `S'`, as for a modification witness (`IsModification.Witness.dense_preimage`), the strict
transform of `𝟙 S` is the zero ideal sheaf on `S ×_S S' ≅ S'`: the dense open `φ⁻¹(U)` of the
reduced scheme `S'` is scheme-theoretically dense. -/
theorem strictTransform_id [IsReduced S'] (h : Dense (SetLike.coe (φ ⁻¹ᵁ U))) :
    strictTransform (𝟙 S) φ U = ⊥ := by
  have : IsReduced (pullback (𝟙 S) φ) := isReduced_of_isOpenImmersion (pullback.snd (𝟙 S) φ)
  have hd : Dense (SetLike.coe (strictTransformOpen (𝟙 S) φ U)) := by
    rw [strictTransformOpen_eq_preimage_snd]
    exact h.preimage (pullback.snd (𝟙 S) φ).isOpenEmbedding.isOpenMap
  have : IsDominant (strictTransformOpen (𝟙 S) φ U).ι := AlgebraicGeometry.Opens.isDominant_ι hd
  have := IsSchemeTheoreticallyDominant.of_isDominant (strictTransformOpen (𝟙 S) φ U).ι
  exact (strictTransformOpen (𝟙 S) φ U).ι.ker_eq_bot

/-- **The strict transform along a blowup is the blowup of the inverse image of the centre.** For
the blowup `b : Bl_I S ⟶ S` of an ideal sheaf `I` and the open `U = S ∖ V(I)`, the strict transform
of `f : X ⟶ S` is the ideal sheaf of the closed immersion `Bl_{I.comap f} X ⟶ X ×_S Bl_I S`
(Stacks, Lemma 31.34.2 (080E)). -/
@[stacks 080E]
theorem strictTransform_eq_blowup (I : S.IdealSheafData) :
    strictTransform f I.blowupToBase I.support.compl = (I.blowupBaseChangeHom f).ker :=
  (I.ker_blowupBaseChangeHom f).symm

end TauCeti.AlgebraicGeometry
