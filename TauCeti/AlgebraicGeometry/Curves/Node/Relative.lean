/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Locality
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Base

/-!
# Nodal relative curves over an arbitrary base

A morphism of schemes is at worst nodal of relative dimension one when this can be checked after
restriction to affine opens of its target.  On an affine base this agrees with the
scheme-theoretic criterion: the morphism is syntomic of relative dimension one and its relative
singular subscheme is unramified over the base.

The affine-local formulation makes nodality a morphism property.  It is invariant under
isomorphism, local on both source and target, stable under arbitrary base change, and contains
smooth morphisms of relative dimension one.  These are the closure properties needed to use
nodal curves in families over nonaffine bases.

On an affine open `U` of a nodal relative curve over `Spec R`, the quotient of `Γ(X, U)` by the
ideal of the singular locus is unramified over `R`
(`AlgebraicGeometry.Scheme.formallyUnramified_quotient_singularLocus_ideal`).

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- The affine-target nodal-curve property.  The existential presentation of the affine target
by a spectrum makes the definition independent of the chosen affine presentation. -/
def affineAtWorstNodalOfRelativeDimensionOne : AffineTargetMorphismProperty :=
  fun _ Y f _ ↦ ∃ (R : Type u) (_ : CommRing R) (e : Y ≅ Spec (.of R)),
    AffineAtWorstNodalOfRelativeDimensionOne (f ≫ e.hom)

private theorem affineAtWorstNodalOfRelativeDimensionOne_source_iso
    {X Y S : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ S) [IsAffine S]
    (h : affineAtWorstNodalOfRelativeDimensionOne f) :
    affineAtWorstNodalOfRelativeDimensionOne (e.hom ≫ f) := by
  obtain ⟨R, _, i, hi⟩ := h
  refine ⟨R, inferInstance, i, ?_⟩
  exact hi.comp_of_etale e.hom

private theorem affineAtWorstNodalOfRelativeDimensionOne_target_iso
    {X Y S : Scheme.{u}} (e : Y ≅ S) (f : X ⟶ Y) [IsAffine Y]
    (h : affineAtWorstNodalOfRelativeDimensionOne f) :
    @affineAtWorstNodalOfRelativeDimensionOne X S (f ≫ e.hom) (.of_isIso e.inv) := by
  obtain ⟨R, _, i, hi⟩ := h
  refine ⟨R, inferInstance, e.symm ≪≫ i, ?_⟩
  have heq : f ≫ e.hom ≫ (e.symm ≪≫ i).hom = f ≫ i.hom := by simp
  rw [Category.assoc, heq]
  exact hi

instance : affineAtWorstNodalOfRelativeDimensionOne.toProperty.RespectsIso :=
  AffineTargetMorphismProperty.respectsIso_mk
    affineAtWorstNodalOfRelativeDimensionOne_source_iso
    affineAtWorstNodalOfRelativeDimensionOne_target_iso

private theorem AffineAtWorstNodalOfRelativeDimensionOne.of_target_iso
    {R R' : Type u} [CommRing R] [CommRing R'] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (h : AffineAtWorstNodalOfRelativeDimensionOne f)
    (e : Spec (.of R') ≅ Spec (.of R)) (f' : X ⟶ Spec (.of R'))
    (w : f' ≫ e.hom = f) : AffineAtWorstNodalOfRelativeDimensionOne f' := by
  let _ : Algebra R R' := (Spec.fullyFaithful.preimage e.hom).unop.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap R R')) = e.hom := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Spec.map_preimage_unop e.hom
  let _ : X.Over (Spec (.of R)) := ⟨f⟩
  let _ : X.Over (Spec (.of R')) := ⟨f'⟩
  have H : IsPullback (𝟙 X) f' f
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [hmap]
    exact IsPullback.of_horiz_isIso ⟨by simp [w]⟩
  exact h.of_isPullback H

/-- On an affine target, the affine-target criterion can be tested using the canonical
presentation by the spectrum of global sections. -/
theorem affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec
    {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) :
    affineAtWorstNodalOfRelativeDimensionOne f ↔
      AffineAtWorstNodalOfRelativeDimensionOne (f ≫ Y.isoSpec.hom) := by
  constructor
  · rintro ⟨R, _, e, h⟩
    let φ : Spec (.of Γ(Y, ⊤)) ≅ Spec (.of R) := Y.isoSpec.symm ≪≫ e
    exact h.of_target_iso φ (f ≫ Y.isoSpec.hom) (by simp [φ])
  · exact fun h ↦ ⟨Γ(Y, ⊤), inferInstance, Y.isoSpec, h⟩

private theorem AffineAtWorstNodalOfRelativeDimensionOne.postcomp_openImmersion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of S)}
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (h : AffineAtWorstNodalOfRelativeDimensionOne f) :
    AffineAtWorstNodalOfRelativeDimensionOne
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let _ : X.Over (Spec (.of S)) := ⟨f⟩
  let _ : X.Over (Spec (.of R)) :=
    ⟨f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  have hfS : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of S)) := h.syntomic
  have hfR : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) :=
    (HasRingHomProperty.respects_isOpenImmersion
      (P := @SyntomicOfRelativeDimension 1)
      (RingHom.locally_stableUnderCompositionWithLocalizationAwaySource
        (isStandardSyntomicOfRelativeDimension_stableUnderCompositionWithLocalizationAway 1).left)
      ).postcomp _ (inferInstance : IsOpenImmersion _) _ hfS
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of S)) := hfS
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hfR
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk hfR ?_
  have hform : FormallyUnramified
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := inferInstance
  have : Algebra.FormallyUnramified R S := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)] at hform
    exact RingHom.formallyUnramified_algebraMap.mp hform
  have hsing := Scheme.singularLocus_eq_of_formallyUnramified_base
    (R := R) (S := S) (X := X) rfl
  rw [hsing]
  simpa only [Category.assoc] using
    MorphismProperty.comp_mem @Unramified
      ((X.singularLocus S).subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      h.unramified_singularLocus inferInstance

private theorem affineAtWorstNodalOfRelativeDimensionOne_postcomp_of_isOpenImmersion
    {X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : X ⟶ Y) (i : Y ⟶ Z) [IsOpenImmersion i]
    (h : affineAtWorstNodalOfRelativeDimensionOne f) :
    affineAtWorstNodalOfRelativeDimensionOne (f ≫ i) := by
  obtain ⟨S, _, e, he⟩ := h
  let _ : Algebra Γ(Z, ⊤) S :=
    (Spec.fullyFaithful.preimage (e.inv ≫ i ≫ Z.isoSpec.hom)).unop.hom.toAlgebra
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤) S)) =
      e.inv ≫ i ≫ Z.isoSpec.hom := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Spec.map_preimage_unop (e.inv ≫ i ≫ Z.isoSpec.hom)
  let _ : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤) S))) := hmap ▸ inferInstance
  refine ⟨Γ(Z, ⊤), inferInstance, Z.isoSpec, ?_⟩
  simpa only [hmap, Category.assoc, Iso.hom_inv_id_assoc] using
    he.postcomp_openImmersion (R := Γ(Z, ⊤))

private theorem affineAtWorstNodalOfRelativeDimensionOne_comp_of_isOpenImmersion
    {X Y Z : Scheme.{u}} [IsAffine Z]
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Z)
    (h : affineAtWorstNodalOfRelativeDimensionOne f) :
    affineAtWorstNodalOfRelativeDimensionOne (i ≫ f) := by
  rw [affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec] at h ⊢
  exact h.comp_of_etale i

private theorem affineAtWorstNodalOfRelativeDimensionOne_of_openCover
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (U : X.OpenCover)
    (h : ∀ j, affineAtWorstNodalOfRelativeDimensionOne (U.f j ≫ f)) :
    affineAtWorstNodalOfRelativeDimensionOne f := by
  exact (affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec f).mpr
    (AffineAtWorstNodalOfRelativeDimensionOne.of_openCover U fun j ↦
      (affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec (U.f j ≫ f)).mp (h j))

private theorem affineAtWorstNodalOfRelativeDimensionOne_of_isPullback
    {P X Y S : Scheme.{u}} [IsAffine X] [IsAffine S]
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback fst snd f g) (hg : affineAtWorstNodalOfRelativeDimensionOne g) :
    affineAtWorstNodalOfRelativeDimensionOne fst := by
  obtain ⟨R, _, e, he⟩ := hg
  let _ : Algebra R Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (f ≫ e.hom).appTop).hom.toAlgebra
  refine ⟨Γ(X, ⊤), inferInstance, X.isoSpec, ?_⟩
  have halg : algebraMap R Γ(X, ⊤) =
      ((Scheme.ΓSpecIso (.of R)).inv ≫ (f ≫ e.hom).appTop).hom := rfl
  have hX : f ≫ e.hom = X.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) := by
    rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, Scheme.isoSpec_hom,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  let _ : P.Over (Spec (.of Γ(X, ⊤))) := ⟨fst ≫ X.isoSpec.hom⟩
  let _ : Y.Over (Spec (.of R)) := ⟨g ≫ e.hom⟩
  have H' : IsPullback snd (P ↘ Spec (.of Γ(X, ⊤))) (Y ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))) :=
    H.flip.of_iso (Iso.refl _) (Iso.refl _) X.isoSpec e
      (by simp) rfl rfl hX
  exact he.of_isPullback H'

/-- The affine-target nodal criterion is stable under base change between affine bases. -/
theorem affineAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange :
    affineAtWorstNodalOfRelativeDimensionOne.IsStableUnderBaseChange := by
  intro Z X Y S _ _ f g f' g' H hg
  exact affineAtWorstNodalOfRelativeDimensionOne_of_isPullback H hg

instance : affineAtWorstNodalOfRelativeDimensionOne.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    affineAtWorstNodalOfRelativeDimensionOne_of_isPullback
      (isPullback_morphismRestrict f (Y.basicOpen r)) hf
  of_basicOpenCover {X Y} _ f s hs h := by
    let U : s → X.Opens := fun r ↦ f ⁻¹ᵁ Y.basicOpen r.1
    have hbasic : ⨆ r : s, Y.basicOpen r.1 = ⊤ :=
      (isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs
    have hU : ⨆ r, U r = ⊤ := by
      rw [← f.preimage_iSup, hbasic]
      simp
    apply affineAtWorstNodalOfRelativeDimensionOne_of_openCover f
      (X.openCoverOfIsOpenCover U hU)
    intro r
    have hr := affineAtWorstNodalOfRelativeDimensionOne_postcomp_of_isOpenImmersion
      (f ∣_ Y.basicOpen r.1) (Y.basicOpen r.1).ι (h r)
    -- By definition of `Scheme.openCoverOfIsOpenCover`, the `r`-th component of the cover is
    -- the open subscheme `U r = f ⁻¹ᵁ Y.basicOpen r` with map its inclusion `(U r).ι` (see
    -- `Scheme.openCoverOfIsOpenCover_X` and `Scheme.openCoverOfIsOpenCover_f`). The source
    -- scheme depends on the component, so we unfold both at once rather than rewriting.
    change affineAtWorstNodalOfRelativeDimensionOne
      ((f ⁻¹ᵁ Y.basicOpen r.1).ι ≫ f)
    -- `morphismRestrict_ι` identifies this composite with `(f ∣_ Y.basicOpen r) ≫ ι`.
    simpa only [morphismRestrict_ι] using hr

/-- Being at worst nodal of relative dimension one is the affine-local extension of the
scheme-theoretic criterion over spectra. -/
def AtWorstNodalOfRelativeDimensionOne : MorphismProperty Scheme.{u} :=
  targetAffineLocally affineAtWorstNodalOfRelativeDimensionOne

instance : HasAffineProperty (@AtWorstNodalOfRelativeDimensionOne.{u})
    affineAtWorstNodalOfRelativeDimensionOne where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := rfl

/-- On an affine target, the global nodal property is exactly the scheme-theoretic
criterion after any chosen presentation of the target as a spectrum. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_of_isAffine
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) (e : Y ≅ Spec (.of R)) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      AffineAtWorstNodalOfRelativeDimensionOne (f ≫ e.hom) := by
  rw [HasAffineProperty.iff_of_isAffine
    (P := @AtWorstNodalOfRelativeDimensionOne.{u})
    (Q := affineAtWorstNodalOfRelativeDimensionOne)]
  constructor
  · intro h
    have hc := (affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec f).mp h
    exact hc.of_target_iso (e.symm.trans Y.isoSpec) (f ≫ e.hom) (by simp)
  · intro h
    apply (affineAtWorstNodalOfRelativeDimensionOne_iff_isoSpec f).mpr
    exact h.of_target_iso (Y.isoSpec.symm.trans e) (f ≫ Y.isoSpec.hom) (by simp)

/-- Being at worst nodal of relative dimension one is stable under arbitrary base change. -/
instance AtWorstNodalOfRelativeDimensionOne.isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@AtWorstNodalOfRelativeDimensionOne.{u}) :=
  HasAffineProperty.isStableUnderBaseChange
    (P := @AtWorstNodalOfRelativeDimensionOne.{u})
    (Q := affineAtWorstNodalOfRelativeDimensionOne)
    affineAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange

/-- Being at worst nodal of relative dimension one is local on the source. -/
instance AtWorstNodalOfRelativeDimensionOne.isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@AtWorstNodalOfRelativeDimensionOne.{u}) := by
  apply HasAffineProperty.isZariskiLocalAtSource
    (P := @AtWorstNodalOfRelativeDimensionOne.{u})
    (Q := affineAtWorstNodalOfRelativeDimensionOne)
  intro X Y f _ U
  constructor
  · intro h j
    exact affineAtWorstNodalOfRelativeDimensionOne_comp_of_isOpenImmersion
      (U.f j) f h
  · exact affineAtWorstNodalOfRelativeDimensionOne_of_openCover f U

/-- A nodal relative curve is syntomic of relative dimension one. -/
theorem AtWorstNodalOfRelativeDimensionOne.syntomic
    {X Y : Scheme.{u}} {f : X ⟶ Y} (h : AtWorstNodalOfRelativeDimensionOne f) :
    SyntomicOfRelativeDimension 1 f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @SyntomicOfRelativeDimension 1) _ (iSup_affineOpens_eq_top Y)]
  intro U
  obtain ⟨R, _, e, he⟩ := HasAffineProperty.restrict
    (P := @AtWorstNodalOfRelativeDimensionOne.{u})
    (Q := affineAtWorstNodalOfRelativeDimensionOne) h U
  rw [← MorphismProperty.cancel_right_of_respectsIso
    (P := @SyntomicOfRelativeDimension 1) (f ∣_ U.1) e.hom]
  exact he.syntomic

/-- Over an affine open `U` of a nodal relative curve over `Spec R`, the quotient of `Γ(X, U)` by
the ideal of the singular locus is unramified over `R`: it is the ring of functions of the
singular subscheme over `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.formallyUnramified_quotient_singularLocus_ideal
    {R : Type u} [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R))) (U : X.affineOpens) :
    letI : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
    letI : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    Algebra.FormallyUnramified R (Γ(X, U) ⧸ (X.singularLocus R).ideal U) := by
  let : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := hnodal.syntomic
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  set I := X.singularLocus R
  have hAffine : AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) :=
    (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)).mp hnodal
  have hu : FormallyUnramified (I.subschemeι ≫ (X ↘ Spec (.of R))) :=
    hAffine.unramified_singularLocus.toFormallyUnramified
  -- The ring map from `Γ(Spec R, ⊤)` to the functions on the singular subscheme over `U`.
  have hP : ((I.subschemeι ≫ (X ↘ Spec (.of R))).appLE ⊤ (I.subschemeι ⁻¹ᵁ U)
      (by simp)).hom.FormallyUnramified :=
    HasRingHomProperty.appLE (P := @FormallyUnramified) _ hu ⟨⊤, isAffineOpen_top _⟩
      ⟨I.subschemeι ⁻¹ᵁ U, U.2.preimage _⟩ _
  have key : (X ↘ Spec (.of R)).appLE ⊤ U (by simp) ≫ I.subschemeι.app U =
      (I.subschemeι ≫ (X ↘ Spec (.of R))).appLE ⊤ (I.subschemeι ⁻¹ᵁ U) (by simp) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← key, I.subschemeι_app] at hP
  -- Composing with `R ≅ Γ(Spec R, ⊤)` and `Γ(I.subscheme, ι ⁻¹ U) ≅ Γ(X, U) ⧸ I(U)` gives the
  -- algebra map.
  have hiso := RingHom.FormallyUnramified.of_surjective
    (I.subschemeObjIso U).commRingCatIsoToRingEquiv.surjective
  have hiso' := RingHom.FormallyUnramified.of_surjective
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective
  have h := hiso'.comp (hP.comp hiso)
  rw [← RingHom.formallyUnramified_algebraMap]
  convert h using 1
  ext r
  have hb := ConcreteCategory.congr_hom (X.baseRingToStructurePresheaf_app_eq_appLE R U.1) r
  simp only [CommRingCat.comp_apply, RingHom.comp_apply] at hb ⊢
  rw [Iso.inv_hom_id_apply]
  exact congrArg (Ideal.Quotient.mk (I.ideal U)) hb

/-- A smooth morphism of relative dimension one is at worst nodal. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    AtWorstNodalOfRelativeDimensionOne f := by
  rw [HasAffineProperty.eq_targetAffineLocally
    (@AtWorstNodalOfRelativeDimensionOne.{u})
    (Q := affineAtWorstNodalOfRelativeDimensionOne)]
  intro U
  refine ⟨Γ(U.1, ⊤), inferInstance, U.1.toScheme.isoSpec, ?_⟩
  let _ : (f ⁻¹ᵁ U.1).toScheme.Over (Spec (.of Γ(U.1, ⊤))) :=
    ⟨(f ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom⟩
  have hfU : SmoothOfRelativeDimension 1 (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (isPullback_morphismRestrict f U.1).flip inferInstance
  let _ : SmoothOfRelativeDimension 1 (f ∣_ U.1) := hfU
  have hf : SmoothOfRelativeDimension 1
      ((f ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom) := by
    have : SmoothOfRelativeDimension (1 + 0)
        ((f ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom) := inferInstance
    simpa using this
  let _ : SmoothOfRelativeDimension 1
      ((f ⁻¹ᵁ U.1).toScheme ↘ Spec (.of Γ(U.1, ⊤))) := hf
  exact AffineAtWorstNodalOfRelativeDimensionOne.of_smooth

/-- The standard node chart is a nodal relative curve. -/
theorem _root_.TauCeti.NodeAlgebra.atWorstNodalOfRelativeDimensionOne
    {R : Type u} [CommRing R] (a : R) :
    AtWorstNodalOfRelativeDimensionOne
      (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) := by
  apply (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)).mpr
  simpa using NodeAlgebra.affineAtWorstNodalOfRelativeDimensionOne a

end TauCeti.AlgebraicGeometry
