/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.PresentationLimit
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport

/-!
# Morphisms of presentation-limit pre-adic spaces

A continuous map of Huber rings carrying `A⁺` into `B⁺` induces a morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)`. This file packages the existing morphism of presentation-limit
structure presheaves as a morphism of pre-adic spaces. The main point is compatibility with the
canonical stalk valuations, proved on rational germs using base change for completed rational
localizations.

Like `presentationLimitPresheafComap`, the construction assumes that the structure presheaf of
`Spa(B, B⁺)` is a sheaf, and nothing more: `φ` need not be adic. Every point of `Spa(B, B⁺)` over a
rational open `R(T/s)` of `Spa(A, A⁺)` has a rational neighbourhood `R(q)` inside the preimage of
`R(T/s)`, and the stalk valuations are compared through the geometric base change
`A⟨T/s⟩ → B⟨q⟩`.

The comparison of stalk valuations only uses that the map of sections is the geometric base change
`A⟨T/s⟩ → B⟨q⟩` on rational opens. For mutually inverse continuous ring homomorphisms the
transport `presentationLimitPresheafIsoPushforward` of the structure presheaf has this property
without any sheaf condition, so an isomorphism of Huber pairs induces an isomorphism of pre-adic
spaces. This applies, for instance, to the Frobenius automorphism of `Spa(A_inf, A_inf)`, where
`A_inf` is not a Tate ring, so that Tate acyclicity does not make its structure presheaf a sheaf.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitPresheafedSpaceComap`: the underlying morphism of
  presheafed spaces.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap`: the induced morphism of
  pre-adic spaces.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComapIso`: the isomorphism of pre-adic
  spaces induced by mutually inverse continuous ring homomorphisms.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_id`,
  `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComap_comp`: the construction is
  contravariantly functorial.
* `presentationLimitRationalGerm_comp_stalkMap_presentationLimitPreAdicSpaceComap`: on the germs
  of a rational open, the stalk maps are the base change of completed rational localisations.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComapIso_hom_toHom`: the isomorphism is
  the map of adic spectra on points and the transport of the structure presheaf on sections.
* `TauCeti.ValuationSpectrum.presentationLimitPreAdicSpaceComapIso_inv_base`: on points, its inverse
  is the map of adic spectra induced by `ψ`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open TauCeti TauCeti.Huber TauCeti.Huber.PairOfDefinition

public section

namespace TauCeti.ValuationSpectrum

universe v
variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A}

variable {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  {P' : PairOfDefinition B} {Bplus : Subring B}

/-- The ring homomorphism of completed rational localizations underlying a morphism
`g : A⟨p⟩ ⟶ B⟨q⟩`, transported along `Presentation.completionLocObjCommRingCatIso`. -/
private noncomputable def completionLocRingHom {p : Presentation P} {q : Presentation P'}
    (g : p.completionLocObj ⟶ q.completionLocObj) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    UniformSpace.Completion (Localization.Away p.den) →+*
      UniformSpace.Completion (Localization.Away q.den) :=
  letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  ((Presentation.completionLocObjCommRingCatIso p).inv ≫
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map g ≫
    (Presentation.completionLocObjCommRingCatIso q).hom).hom

/-- `completionLocRingHom g` is the ring map underlying `g`, transported along
`completionLocObj_obj` in `TopCommRingCat`. -/
private theorem completionLocRingHom_eq {p : Presentation P} {q : Presentation P'}
    (g : p.completionLocObj ⟶ q.completionLocObj) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    completionLocRingHom g =
      (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm ≫ g.hom ≫
        eqToHom (completionLocObj_obj P' q.num q.den _ q.hasDenominatorPower)).1 := by
  rw [completionLocRingHom]
  simp only [Functor.comp_map, Presentation.completionLocObjCommRingCatIso_inv,
    Presentation.completionLocObjCommRingCatIso_hom]
  -- `forget₂ TopCommRingCat CommRingCat` and `isCompleteSeparated.ι` act on morphisms by
  -- forgetting continuity and the property, so both sides are the same ring homomorphism.
  rfl

/-- The ring homomorphism underlying a morphism of completed rational localizations is
continuous. -/
private theorem continuous_completionLocRingHom {p : Presentation P} {q : Presentation P'}
    (g : p.completionLocObj ⟶ q.completionLocObj) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    Continuous (completionLocRingHom g) := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  rw [completionLocRingHom_eq]
  exact (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm ≫ g.hom ≫
    eqToHom (completionLocObj_obj P' q.num q.den _ q.hasDenominatorPower)).2

/-- A morphism `g : A⟨p⟩ ⟶ B⟨q⟩` carrying the structure map of `p` to that of `q` after `φ` does so
on underlying ring homomorphisms. -/
private theorem completionLocRingHom_comp_toCompletionLoc (φ : A →+* B) (hφ : Continuous φ)
    {p : Presentation P} {q : Presentation P'} (g : p.completionLocObj ⟶ q.completionLocObj)
    (hg : p.toCompletionLocTopHom ≫ g.hom =
      (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫ q.toCompletionLocTopHom) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    (completionLocRingHom g).comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) =
      (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower).comp φ := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have h := congrArg (fun k ↦ k ≫
    eqToHom (completionLocObj_obj P' q.num q.den _ q.hasDenominatorPower)) hg
  rw [Presentation.toCompletionLocTopHom_eq, Presentation.toCompletionLocTopHom_eq] at h
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h
  rw [completionLocRingHom_eq]
  exact congrArg Subtype.val h

/-- Composing with `Presentation.completionLocObjCommRingCatIso` turns a morphism `g` into
`completionLocRingHom g`. -/
private theorem completionLocObjCommRingCatIso_hom_comp_ofHom_completionLocRingHom
    {p : Presentation P} {q : Presentation P'} (g : p.completionLocObj ⟶ q.completionLocObj) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    (Presentation.completionLocObjCommRingCatIso p).hom ≫
        CommRingCat.ofHom (completionLocRingHom g) =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map g ≫
        (Presentation.completionLocObjCommRingCatIso q).hom := by
  rw [completionLocRingHom, CommRingCat.ofHom_hom, Iso.hom_inv_id_assoc]

/-- The point of `Spa(A⟨p⟩, A⟨p⟩⁺)` attached to `x ∈ R(p)` pulls back along the structure
map to `x`. -/
private theorem comap_toCompletionLoc_spaCompletedLocalizationHomeomorph_symm
    (hP : P.ringOfDefinition ≤ Aplus) (p : Presentation P) (x : spa Aplus)
    (hx : x ∈ spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    comap (toCompletionLoc P p.num p.den _ p.hasDenominatorPower)
        ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
          p.hasDenominatorPower).symm ⟨x, mem_spaBasicOpen.mp hx⟩).1 = x := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have hw := spaCompletedLocalizationHomeomorph_apply P Aplus hP p.num p.den _
    p.hasDenominatorPower ((spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
      p.hasDenominatorPower).symm ⟨x, mem_spaBasicOpen.mp hx⟩)
  rw [Homeomorph.apply_symm_apply] at hw
  have hxw := congrArg (fun z ↦ z.1.1) hw
  simp only [spaLocToRationalSubset_val, spaComapLoc_val] at hxw
  exact hxw.symm

/-- Pulling a rational-localization point back along a morphism `g : A⟨p⟩ ⟶ B⟨q⟩` of completed
rational localizations over `φ` gives the rational-localization point attached to the pulled-back
valuation. This applies to the base changes `Presentation.mapHom` and
`Presentation.mapHomOfSubset`. -/
theorem comap_map_rationalLocalizationPoint (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    {p : Presentation P} {q : Presentation P'} (g : p.completionLocObj ⟶ q.completionLocObj)
    (hg : p.toCompletionLocTopHom ≫ g.hom =
      (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫ q.toCompletionLocTopHom)
    (x : spa Bplus) (hx : x ∈ spaBasicOpen Bplus q.num q.den)
    (hy : spaComap φ hφ Aplus Bplus hplus x ∈ spaBasicOpen Aplus p.num p.den) :
    comap ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        g).hom
      (rationalLocalizationPoint hP' q x hx) =
      rationalLocalizationPoint hP p (spaComap φ hφ Aplus Bplus hplus x) hy := by
  let _ := locUniformSpace P p.num p.den (Localization.Away p.den) p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den (Localization.Away q.den) q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  set y := spaComap φ hφ Aplus Bplus hplus x with hy_def
  set w := (spaCompletedLocalizationHomeomorph P' Bplus hP' q.num q.den _
    q.hasDenominatorPower).symm ⟨x, mem_spaBasicOpen.mp hx⟩
  have hcomp := completionLocRingHom_comp_toCompletionLoc φ hφ g hg
  have hwx : comap (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower) w.1 = x :=
    comap_toCompletionLoc_spaCompletedLocalizationHomeomorph_symm hP' q x hx
  -- Pulling `w` back along the base change gives a point of `Spa(A⟨p⟩, A⟨p⟩⁺)` over `y`.
  have hcomap : comap ((completionLocRingHom g).comp
      (toCompletionLoc P p.num p.den _ p.hasDenominatorPower)) w.1 = y.1 := by
    rw [hcomp, comap_comp, Function.comp_apply, hwx, hy_def, spaComap_val]
  have hmem : comap (completionLocRingHom g) w.1 ∈
      spa (completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower) := by
    refine comap_mem_spa_completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower _
      (continuous_completionLocRingHom g) ((mem_spa_iff _ _).mp w.2).1
      (fun a ha ↦ ?_) ?_
    · rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
      exact ((mem_spa_iff _ _).mp w.2).2 _
        (toCompletionLoc_mem_completedPlusSubring P' Bplus q.num q.den _
          q.hasDenominatorPower (hplus a ha))
    · rw [hcomap]
      exact mem_spaBasicOpen.mp hy
  have hpt :
      (spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
        p.hasDenominatorPower).symm ⟨y, mem_spaBasicOpen.mp hy⟩ =
        ⟨comap (completionLocRingHom g) w.1, hmem⟩ := by
    rw [Homeomorph.symm_apply_eq]
    refine Subtype.ext (Subtype.ext ?_)
    rw [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, ← hcomap,
      spaComapLoc_val, comap_comp, Function.comp_apply]
  -- Both points are now pullbacks of `w`; compare the two composite ring maps.
  rw [rationalLocalizationPoint_def, rationalLocalizationPoint_def, hpt, comap_hom_comap_hom,
    ← completionLocObjCommRingCatIso_hom_comp_ofHom_completionLocRingHom, ← comap_hom_comap_hom,
    CommRingCat.hom_ofHom]

/-- The morphism of presentation-limit presheafed spaces induced contravariantly by a continuous
ring homomorphism preserving the chosen rings of integral elements. -/
@[expose] noncomputable def presentationLimitPresheafedSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace ⟶
      (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace where
  base := spaComapTopHom φ hφ hplus
  c := presentationLimitPresheafComap φ hφ hplus hBplus hsheaf

/-- The continuous map underlying `presentationLimitPresheafedSpaceComap` is the induced map
`spaComapTopHom` of adic spectra. -/
@[simp]
theorem presentationLimitPresheafedSpaceComap_base
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    (presentationLimitPresheafedSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).base =
      spaComapTopHom φ hφ hplus :=
  rfl

/-- The map of structure presheaves underlying `presentationLimitPresheafedSpaceComap` is
`presentationLimitPresheafComap`. -/
@[simp]
theorem presentationLimitPresheafedSpaceComap_c
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    (presentationLimitPresheafedSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).c =
      presentationLimitPresheafComap φ hφ hplus hBplus hsheaf :=
  rfl

/-! ### Compatibility with the stalk valuations

The stalk valuations are compared on rational germs, and the comparison only uses one property of
the map of sections: restricted from a rational open `R(p)` of `Spa(A, A⁺)` to a rational open
`R(q)` of `Spa(B, B⁺)` inside its preimage, it is the geometric base change `A⟨p⟩ → B⟨q⟩`. The
argument is therefore carried out for an arbitrary morphism of presheaves
`c : 𝒪_{Spa A} ⟶ f_* 𝒪_{Spa B}` with this property (`IsBaseChangeOnRational`). It applies to
`presentationLimitPresheafComap`, and to the transport `presentationLimitPresheafIsoPushforward`
along an isomorphism, which needs no sheaf condition.

Every point `x` of `Spa(B, B⁺)` over a rational open `R(p)` has a rational neighbourhood `R(q)`
inside the preimage of `R(p)`, so no condition on `φ` beyond continuity is needed. -/

section StalkValuation

variable (φ : A →+* B) (hφ : Continuous φ)
  (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
  (c : presentationLimitPresheaf P Aplus ⟶
    (TopCat.Presheaf.pushforward _ (spaComapTopHom φ hφ hplus)).obj
      (presentationLimitPresheaf P' Bplus))

/-- The morphism of presheafed spaces of rings with underlying map `spaComapTopHom φ` and map of
sections `c`, after forgetting the topology on sections. -/
private noncomputable def ringPresheafedSpaceHom :
    ({ carrier := TopCat.of ↥(spa Bplus)
       presheaf := presentationLimitPresheafInCommRingCat P' Bplus } :
      PresheafedSpace CommRingCat.{v}) ⟶
    ({ carrier := TopCat.of ↥(spa Aplus)
       presheaf := presentationLimitPresheafInCommRingCat P Aplus } :
      PresheafedSpace CommRingCat.{v}) where
  base := spaComapTopHom φ hφ hplus
  c := eqToHom (presentationLimitPresheafInCommRingCat_def P Aplus) ≫
    Functor.whiskerRight c
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat) ≫
    eqToHom (by
      rw [presentationLimitPresheafInCommRingCat_def]
      rfl)

private theorem ringPresheafedSpaceHom_c_app (U : (Opens ↥(spa Aplus))ᵒᵖ) :
    (ringPresheafedSpaceHom φ hφ hplus c).c.app U =
      eqToHom (presentationLimitPresheafInCommRingCat_obj P Aplus U) ≫
        (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (eqToHom (presentationLimitPresheaf_obj P Aplus U).symm ≫ c.app U ≫
            eqToHom (presentationLimitPresheaf_obj P' Bplus _)) ≫
        eqToHom (presentationLimitPresheafInCommRingCat_obj P' Bplus _).symm := by
  dsimp only [ringPresheafedSpaceHom]
  rw [NatTrans.comp_app, NatTrans.comp_app, eqToHom_app, eqToHom_app,
    Functor.whiskerRight_app]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- The map of sections `c` is the geometric base change on rational opens: for a rational open
`R(p)` of `Spa(A, A⁺)` and a rational open `R(q)` of `Spa(B, B⁺)` inside its preimage, the
component of `c` on `R(p)`, restricted to `R(q)`, is the geometric base change `A⟨p⟩ → B⟨q⟩` under
the rational comparison isomorphisms. -/
private def IsBaseChangeOnRational : Prop :=
  ∀ (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (q : Presentation P') (hq : IsOpen (Ideal.span (q.num : Set B) : Set B))
    (hpq : spaBasicOpen Bplus q.num q.den ≤
      (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus p.num p.den)),
    (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
        eqToHom (presentationLimitPresheaf_obj P Aplus
          (Opposite.op (spaBasicOpen Aplus p.num p.den))).symm ≫
        c.app (Opposite.op (spaBasicOpen Aplus p.num p.den)) ≫
        eqToHom (presentationLimitPresheaf_obj P' Bplus _) ≫
        presentationLimitMap hpq ≫ (presentationLimitRationalIso Bplus hBplus q hq).hom =
      p.mapHomOfSubset φ hφ Aplus Bplus hBplus q
        ((spaBasicOpen_le_map_spaBasicOpen_iff φ hφ hplus).mp hpq)

variable {φ hφ hplus hAplus hBplus c}

/-- After forgetting topology, the component of `ringPresheafedSpaceHom` on `R(p)`, restricted to a
rational open `R(q)` inside its preimage, is the geometric base change `A⟨p⟩ → B⟨q⟩`, under the
rational comparison isomorphisms. -/
private theorem IsBaseChangeOnRational.rationalIsoInCommRingCat_inv_comp_c_app_comp_map
    (hc : IsBaseChangeOnRational φ hφ hplus hAplus hBplus c)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (q : Presentation P') (hq : IsOpen (Ideal.span (q.num : Set B) : Set B))
    (hpq : spaBasicOpen Bplus q.num q.den ≤
      (Opens.map (ringPresheafedSpaceHom φ hφ hplus c).base).obj
        (spaBasicOpen Aplus p.num p.den)) :
    (presentationLimitRationalIsoInCommRingCat hAplus p hp).inv ≫
        (ringPresheafedSpaceHom φ hφ hplus c).c.app
          (Opposite.op (spaBasicOpen Aplus p.num p.den)) ≫
        (presentationLimitPresheafInCommRingCat P' Bplus).map (homOfLE hpq).op =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (p.mapHomOfSubset φ hφ Aplus Bplus hBplus q
            ((spaBasicOpen_le_map_spaBasicOpen_iff φ hφ hplus).mp hpq)) ≫
        (presentationLimitRationalIsoInCommRingCat hBplus q hq).inv := by
  rw [ringPresheafedSpaceHom_c_app]
  -- Unfold `base` to `spaComapTopHom`, the form in which
  -- `presentationLimitPresheafInCommRingCat_map` is stated.
  dsimp only [ringPresheafedSpaceHom] at hpq ⊢
  rw [← cancel_mono (presentationLimitRationalIsoInCommRingCat hBplus q hq).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [presentationLimitRationalIsoInCommRingCat_hom,
    reassoc_of% presentationLimitPresheafInCommRingCat_map P' Bplus (homOfLE hpq).op]
  simpa only [presentationLimitRationalIsoInCommRingCat_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using congrArg
      (fun k ↦ (TopCommRingCat.isCompleteSeparated.ι ⋙
        forget₂ TopCommRingCat CommRingCat).map k) (hc p hp q hq hpq)

/-- The stalk map of `ringPresheafedSpaceHom` carries the germ of the rational open `R(p)` to the
germ of a rational open `R(q)` inside its preimage after the geometric base change
`A⟨p⟩ → B⟨q⟩`. -/
private theorem IsBaseChangeOnRational.presentationLimitRationalGerm_comp_stalkMap
    (hc : IsBaseChangeOnRational φ hφ hplus hAplus hBplus c)
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (q : Presentation P') (hq : IsOpen (Ideal.span (q.num : Set B) : Set B))
    (hpq : spaBasicOpen Bplus q.num q.den ≤
      (Opens.map (ringPresheafedSpaceHom φ hφ hplus c).base).obj
        (spaBasicOpen Aplus p.num p.den)) (x : spa Bplus)
    (hy : (ringPresheafedSpaceHom φ hφ hplus c).base x ∈ spaBasicOpen Aplus p.num p.den)
    (hx : x ∈ spaBasicOpen Bplus q.num q.den) :
    presentationLimitRationalGerm hAplus p hp _ hy ≫
        (ringPresheafedSpaceHom φ hφ hplus c).stalkMap x =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (p.mapHomOfSubset φ hφ Aplus Bplus hBplus q
            ((spaBasicOpen_le_map_spaBasicOpen_iff φ hφ hplus).mp hpq)) ≫
        presentationLimitRationalGerm hBplus q hq x hx := by
  rw [presentationLimitRationalGerm_def, presentationLimitRationalGerm_def, Category.assoc,
    PresheafedSpace.stalkMap_germ (ringPresheafedSpaceHom φ hφ hplus c) _ x hy,
    ← (presentationLimitPresheafInCommRingCat P' Bplus).germ_res (homOfLE hpq) x hx,
    reassoc_of% hc.rationalIsoInCommRingCat_inv_comp_c_app_comp_map p hp q hq hpq,
    Functor.comp_map]

variable (φ hφ hplus c) in
/-- Forgetting the topology on sections of the morphism of presheafed spaces with underlying map
`spaComapTopHom φ` and map of sections `c` gives `ringPresheafedSpaceHom`, so the two pull the
canonical stalk valuation back in the same way. -/
private theorem comap_stalkMap_toRingPresheafedSpaceHom (x : spa Bplus) :
    comap ((TauCeti.PreAdicSpace.toRingPresheafedSpaceHom
        ({ base := spaComapTopHom φ hφ hplus, c := c } :
          (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace ⟶
            (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace)).stalkMap x).hom
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) =
      comap ((ringPresheafedSpaceHom φ hφ hplus c).stalkMap x).hom
        (presentationLimitStalkValuation hBplus hP' x) := by
  rw [presentationLimitPreAdicSpace_stalkValuation P' Bplus hBplus hP' x]
  -- `toRingPresheafedSpaceHom` forgets the topology on sections componentwise, which is how
  -- `ringPresheafedSpaceHom` is built from `c`.
  rfl

/-- **A map of sections that is the base change on rational opens preserves the canonical stalk
valuations**: through the stalk map at `x`, the morphism of presheafed spaces with underlying map
`spaComapTopHom φ` and map of sections `c` pulls the stalk valuation at `x` back to the stalk
valuation at its image. -/
private theorem IsBaseChangeOnRational.stalkValuation_eq
    (hc : IsBaseChangeOnRational φ hφ hplus hAplus hBplus c) (x : spa Bplus) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).stalkValuation
        (spaComap φ hφ Aplus Bplus hplus x) =
      comap ((TauCeti.PreAdicSpace.toRingPresheafedSpaceHom
        ({ base := spaComapTopHom φ hφ hplus, c := c } :
          (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace ⟶
            (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace)).stalkMap x).hom
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) := by
  refine (presentationLimitPreAdicSpace_stalkValuation P Aplus hAplus hP
    (spaComap φ hφ Aplus Bplus hplus x)).trans ?_
  rw [comap_stalkMap_toRingPresheafedSpaceHom φ hφ hplus hP hP' c]
  -- Replace the point `spaComap φ hφ Aplus Bplus hplus x` by its definitional form `f.base x`,
  -- the source point of the stalk map `f.stalkMap x`, so that germs at it compose with it.
  let f := ringPresheafedSpaceHom (P := P) (P' := P') φ hφ hplus c
  have hbase : f.base x = spaComap φ hφ Aplus Bplus hplus x := rfl
  cases hbase
  -- Check the pulled-back valuation on the rational germs at `f.base x`, through a rational
  -- neighbourhood `R(q)` of `x` inside the preimage of `R(p)`.
  refine (eq_presentationLimitStalkValuation (x := f.base x) hAplus hP fun p hp hy ↦ ?_).symm
  obtain ⟨q, hq, hx, hpq⟩ := exists_presentation_mem_spaBasicOpen_le P'
    (U := (Opens.map f.base).obj (spaBasicOpen Aplus p.num p.den)) (Opens.mem_map.mpr hy)
  rw [comap_hom_comap_hom, hc.presentationLimitRationalGerm_comp_stalkMap p hp q hq hpq x hy hx,
    ← comap_hom_comap_hom, comap_presentationLimitRationalGerm_presentationLimitStalkValuation]
  exact comap_map_rationalLocalizationPoint φ hφ hplus hP hP' _
    (Presentation.toCompletionLocTopHom_comp_mapHomOfSubset φ hφ Aplus Bplus hBplus p q _) x hx hy

end StalkValuation

/-- `presentationLimitPresheafComap` is the base change on rational opens. -/
private theorem isBaseChangeOnRational_presentationLimitPresheafComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    IsBaseChangeOnRational (P := P) φ hφ hplus hAplus hBplus
      (presentationLimitPresheafComap φ hφ hplus hBplus hsheaf) := fun p hp q hq hpq ↦ by
  simp only [presentationLimitPresheafComap_app, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [presentationLimitRationalIso_hom, presentationLimitComap_comp_map_comp_π_of_subset φ hφ hplus
      hBplus hsheaf ⟨p, hp, le_rfl⟩ hpq ⟨q, hq, le_rfl⟩
      ((spaBasicOpen_le_map_spaBasicOpen_iff φ hφ hplus).mp hpq),
    ← Category.assoc, presentationLimitRationalIso_inv_comp_π, homOfRationalSubsetSubset_self,
    Category.id_comp]

/-- The underlying morphism of presheafed spaces preserves the canonical stalk valuations. -/
theorem presentationLimitPresheafedSpaceComap_stalkValuation
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) (x : spa Bplus) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).stalkValuation
        (spaComap φ hφ Aplus Bplus hplus x) =
      comap ((TauCeti.PreAdicSpace.toRingPresheafedSpaceHom
        (presentationLimitPresheafedSpaceComap φ hφ hplus hAplus hBplus hP hP'
          hsheaf)).stalkMap x).hom
        ((presentationLimitPreAdicSpace P' Bplus hBplus hP').stalkValuation x) :=
  (isBaseChangeOnRational_presentationLimitPresheafComap φ hφ hplus hAplus hBplus
    hsheaf).stalkValuation_eq hP hP' x

/-- The morphism of presentation-limit pre-adic spaces induced contravariantly by a continuous
ring homomorphism preserving the chosen rings of integral elements. -/
noncomputable def presentationLimitPreAdicSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP where
  toHom := presentationLimitPresheafedSpaceComap φ hφ hplus hAplus hBplus hP hP'
    hsheaf
  stalkValuation_eq x :=
    presentationLimitPresheafedSpaceComap_stalkValuation φ hφ hplus hAplus hBplus
      hP hP' hsheaf x

/-- The morphism of presheafed spaces underlying `presentationLimitPreAdicSpaceComap` is
`presentationLimitPresheafedSpaceComap`. -/
@[simp]
theorem presentationLimitPreAdicSpaceComap_toHom
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus)) :
    (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf).toHom =
      presentationLimitPresheafedSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf := by
  rw [presentationLimitPreAdicSpaceComap]

/-- **The stalk maps on rational germs.** Let `R(p)` be a rational open of `Spa(A, A⁺)` and `R(q)` a
rational open of `Spa(B, B⁺)` inside its preimage. At a point `x` of `R(q)`, the stalk map of the
morphism induced by `φ` carries the germ of an element of `A⟨p⟩` to the germ of its image under the
geometric base change `A⟨p⟩ → B⟨q⟩`. -/
theorem presentationLimitRationalGerm_comp_stalkMap_presentationLimitPreAdicSpaceComap
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (p : Presentation P) (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (q : Presentation P') (hq : IsOpen (Ideal.span (q.num : Set B) : Set B))
    (hsub : rationalSubset Bplus q.num q.den ⊆ comap φ ⁻¹' rationalSubset Aplus p.num p.den)
    (x : spa Bplus)
    (hy : (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP'
      hsheaf).base x ∈ spaBasicOpen Aplus p.num p.den)
    (hx : x ∈ spaBasicOpen Bplus q.num q.den) :
    presentationLimitRationalGerm hAplus p hp _ hy ≫
        (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP'
          hsheaf).stalkMap x =
      (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (p.mapHomOfSubset φ hφ Aplus Bplus hBplus q hsub) ≫
        presentationLimitRationalGerm hBplus q hq x hx :=
  -- forgetting the topology on sections of the induced morphism gives `ringPresheafedSpaceHom`
  (congrArg (presentationLimitRationalGerm hAplus p hp _ hy ≫ ·)
    (PreAdicSpace.Hom.stalkMap_def
      (presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf) x)).trans
    ((isBaseChangeOnRational_presentationLimitPresheafComap φ hφ hplus hAplus hBplus
      hsheaf).presentationLimitRationalGerm_comp_stalkMap p hp q hq
        ((spaBasicOpen_le_map_spaBasicOpen_iff φ hφ hplus).mpr hsub) x hy hx)

/-! ### Functoriality -/

/-- **The identity of `A` induces the identity morphism** of `Spa(A, A⁺)`. -/
@[simp]
theorem presentationLimitPreAdicSpaceComap_id (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    presentationLimitPreAdicSpaceComap (P := P) (P' := P) (RingHom.id A) continuous_id
        (fun _ ha ↦ ha) hAplus hAplus hP hP hsheaf =
      𝟙 _ := by
  ext1
  rw [presentationLimitPreAdicSpaceComap_toHom]
  exact PresheafedSpace.ext _ _ spaComapTopHom_id (presentationLimitPresheafComap_id hAplus hsheaf)

section Comp

variable {C : Type v} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  {P'' : PairOfDefinition C} {Cplus : Subring C}

/-- **The morphisms are contravariantly functorial**: for continuous homomorphisms
`φ : A → B` and `ψ : B → C` of Huber rings, the morphism `Spa(C, C⁺) ⟶ Spa(A, A⁺)` induced by
`ψ ∘ φ` is the morphism induced by `ψ` followed by the morphism induced by `φ`. -/
theorem presentationLimitPreAdicSpaceComap_comp
    (φ : A →+* B) (hφ : Continuous φ)
    (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    (ψ : B →+* C) (hψ : Continuous ψ)
    (hplus' : ∀ b ∈ Bplus, ψ b ∈ Cplus)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
    (hCplus : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c)
    (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)
    (hP'' : P''.ringOfDefinition ≤ Cplus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Bplus))
      (presentationLimitPresheaf P' Bplus))
    (hsheaf' : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Cplus))
      (presentationLimitPresheaf P'' Cplus)) :
    presentationLimitPreAdicSpaceComap (P := P) (P' := P'') (ψ.comp φ) (hψ.comp hφ)
        (fun a ha ↦ hplus' (φ a) (hplus a ha)) hAplus hCplus hP hP'' hsheaf' =
      presentationLimitPreAdicSpaceComap ψ hψ hplus' hBplus hCplus hP' hP'' hsheaf' ≫
        presentationLimitPreAdicSpaceComap φ hφ hplus hAplus hBplus hP hP' hsheaf := by
  ext1
  rw [PreAdicSpace.comp_toHom, presentationLimitPreAdicSpaceComap_toHom,
    presentationLimitPreAdicSpaceComap_toHom, presentationLimitPreAdicSpaceComap_toHom]
  exact PresheafedSpace.ext _ _ (spaComapTopHom_comp φ hφ hplus hψ hplus')
    (presentationLimitPresheafComap_comp φ hφ hplus hBplus hsheaf ψ hψ hplus' hCplus
      hsheaf')

end Comp

/-! ### Isomorphisms

Mutually inverse continuous ring homomorphisms `φ : A → B` and `ψ : B → A` carrying the plus rings
into each other induce an isomorphism `Spa(B, B⁺) ≅ Spa(A, A⁺)` of pre-adic spaces. Its map of
sections is the transport `presentationLimitPresheafIsoPushforward`, so unlike
`presentationLimitPreAdicSpaceComap` it needs no sheaf condition on either side. -/

section Iso

variable (φ : A →+* B) (hφ : Continuous φ) (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
  (ψ : B →+* A) (hψ : Continuous ψ) (hψφ : ∀ a, ψ (φ a) = a) (hφψ : ∀ b, φ (ψ b) = b)
  (hplus' : ∀ b ∈ Bplus, ψ b ∈ Aplus)
  (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hBplus : ∀ ⦃b⦄, b ∈ Bplus → IsPowerBounded b)
  (hP : P.ringOfDefinition ≤ Aplus) (hP' : P'.ringOfDefinition ≤ Bplus)

/-- The transport of the structure presheaf along mutually inverse ring homomorphisms is the base
change on rational opens. -/
private theorem isBaseChangeOnRational_presentationLimitPresheafIsoPushforward :
    IsBaseChangeOnRational (P := P) (P' := P') φ hφ hplus hAplus hBplus
      (presentationLimitPresheafIsoPushforward φ hφ hplus ψ hψ hψφ hφψ hplus').hom :=
  fun p hp q hq hpq ↦ by
    classical
    -- the presentation `(ψ(T), ψ(s))` of a rational open inside `R(p)`, for the presentation
    -- `(T, s)` of `R(q)`
    let i := (⟨q, hq, le_rfl⟩ : PresentationIndex (P := P') Bplus
      (spaBasicOpen Bplus q.num q.den)).map (P' := P) ψ hψ (fun I hI ↦ by
        rw [Ideal.map_eq_image_of_surjective ψ (Function.RightInverse.surjective hψφ)]
        exact (IsOpenMap.of_inverse hφ hψφ hφψ) I hI) hplus'
        (V := spaBasicOpen Aplus p.num p.den)
        fun w hw ↦ mem_of_spaComap_mem_map φ hφ hplus ψ hψ hψφ hplus' _ w (hpq hw)
    rw [presentationLimitRationalIso_hom,
      presentationLimitPresheafIsoPushforward_hom_app_comp_map_comp_π φ hφ hplus ψ hψ hψφ hφψ
        hplus' i hpq ⟨q, hq, le_rfl⟩ (by rw [PresentationIndex.map_pres_den, hφψ])
        (fun t ht ↦ by
          rw [PresentationIndex.map_pres_num] at ht
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
          rwa [hφψ]),
      ← Category.assoc, presentationLimitRationalIso_inv_comp_π]
    -- both morphisms `A⟨p⟩ → B⟨q⟩` restrict to `A → B → B⟨q⟩` on `A`
    refine p.hom_ext ?_
    rw [ObjectProperty.FullSubcategory.comp_hom,
      toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc,
      Presentation.toCompletionLocTopHom_comp_mapHom,
      Presentation.toCompletionLocTopHom_comp_mapHomOfSubset]

/-- The morphism of pre-adic spaces underlying `presentationLimitPreAdicSpaceComapIso`: the map of
adic spectra induced by `φ`, with the transport of the structure presheaf along `φ` and `ψ` on
sections. -/
private noncomputable def presentationLimitPreAdicSpaceComapIsoHom :
    presentationLimitPreAdicSpace P' Bplus hBplus hP' ⟶
      presentationLimitPreAdicSpace P Aplus hAplus hP where
  toHom :=
    { base := spaComapTopHom φ hφ hplus
      c := (presentationLimitPresheafIsoPushforward (P := P) (P' := P') φ hφ hplus ψ hψ hψφ hφψ
        hplus').hom }
  stalkValuation_eq x :=
    (isBaseChangeOnRational_presentationLimitPresheafIsoPushforward φ hφ hplus ψ hψ hψφ hφψ hplus'
      hAplus hBplus).stalkValuation_eq hP hP' x

/-- The underlying morphism of presheafed spaces of `presentationLimitPreAdicSpaceComapIsoHom` is
an isomorphism: its map of spaces is the homeomorphism `spaComapTopIso` and its map of sections is
the transport isomorphism. -/
private theorem isIso_presentationLimitPreAdicSpaceComapIsoHom_toHom :
    IsIso (X := (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace)
      (Y := (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace)
      (presentationLimitPreAdicSpaceComapIsoHom φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP
        hP').toHom := by
  let f := (presentationLimitPreAdicSpaceComapIsoHom φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus
    hP hP').toHom
  -- the map of spaces is `spaComapTopHom φ hφ hplus` by construction of
  -- `presentationLimitPreAdicSpaceComapIsoHom`, and that is the forward map of `spaComapTopIso`
  have hbase : f.base = spaComapTopHom φ hφ hplus := rfl
  have : IsIso f.base := by
    rw [hbase, ← spaComapTopIso_hom φ hφ hplus ψ hψ hψφ hφψ hplus']
    exact (spaComapTopIso φ hφ hplus ψ hψ hψφ hφψ hplus').isIso_hom
  have : IsIso f.c := Iso.isIso_hom (presentationLimitPresheafIsoPushforward (P := P) (P' := P') φ
    hφ hplus ψ hψ hψφ hφψ hplus')
  exact PresheafedSpace.isIso_of_components f

/-- **An isomorphism of Huber pairs induces an isomorphism of pre-adic spaces.** Let `φ : A → B`
and `ψ : B → A` be mutually inverse continuous ring homomorphisms carrying `A⁺` into `B⁺` and `B⁺`
into `A⁺`, where the plus rings consist of power-bounded elements and contain the rings of
definition of the pairs of definition `P` and `P'`. Then `Spa(B, B⁺)` and `Spa(A, A⁺)` are
isomorphic in `𝒱^pre`: on points the isomorphism is the map `v ↦ v ∘ φ` of adic spectra
(`presentationLimitPreAdicSpaceComapIso_hom_base`), on sections it is the transport
`presentationLimitPresheafIsoPushforward` (`presentationLimitPreAdicSpaceComapIso_hom_toHom`), and
it matches the stalk valuations. No sheaf condition is assumed. The two pairs of definition are
arbitrary; for `φ = ψ = id` this compares the pre-adic spaces of two pairs of definition of one
Huber ring. -/
noncomputable def presentationLimitPreAdicSpaceComapIso :
    presentationLimitPreAdicSpace P' Bplus hBplus hP' ≅
      presentationLimitPreAdicSpace P Aplus hAplus hP :=
  haveI := PreAdicSpace.isIso_of_isIso_toHom
    (presentationLimitPreAdicSpaceComapIsoHom φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP hP')
    (hf := isIso_presentationLimitPreAdicSpaceComapIsoHom_toHom φ hφ hplus ψ hψ hψφ hφψ hplus'
      hAplus hBplus hP hP')
  asIso (presentationLimitPreAdicSpaceComapIsoHom φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP
    hP')

/-- On points, `presentationLimitPreAdicSpaceComapIso` is the map of adic spectra induced by
`φ`. -/
@[simp]
theorem presentationLimitPreAdicSpaceComapIso_hom_base :
    (presentationLimitPreAdicSpaceComapIso φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP
      hP').hom.base = spaComapTopHom φ hφ hplus :=
  (rfl)

/-- On points, the inverse of `presentationLimitPreAdicSpaceComapIso` is the map of adic spectra
induced by `ψ`. -/
@[simp]
theorem presentationLimitPreAdicSpaceComapIso_inv_base :
    (presentationLimitPreAdicSpaceComapIso φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP
      hP').inv.base = spaComapTopHom ψ hψ hplus' := by
  -- the image of the isomorphism in `TopCat` has the forward map of `spaComapTopIso`, so it is
  -- `spaComapTopIso`, whose inverse is induced by `ψ`
  have h : PreAdicSpace.forgetToTop.mapIso (presentationLimitPreAdicSpaceComapIso φ hφ hplus ψ hψ
      hψφ hφψ hplus' hAplus hBplus hP hP') = spaComapTopIso φ hφ hplus ψ hψ hψφ hφψ hplus' :=
    Iso.ext ((presentationLimitPreAdicSpaceComapIso_hom_base φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus
      hBplus hP hP').trans (spaComapTopIso_hom φ hφ hplus ψ hψ hψφ hφψ hplus').symm)
  rw [← spaComapTopIso_inv φ hφ hplus ψ hψ hψφ hφψ hplus', ← h, Functor.mapIso_inv,
    PreAdicSpace.forgetToTop_map]

/-- The underlying morphism of presheafed spaces of `presentationLimitPreAdicSpaceComapIso` is the
map of adic spectra induced by `φ` on points, with the transport
`presentationLimitPresheafIsoPushforward` of the structure presheaf along `φ` and `ψ` on
sections. -/
theorem presentationLimitPreAdicSpaceComapIso_hom_toHom :
    (presentationLimitPreAdicSpaceComapIso φ hφ hplus ψ hψ hψφ hφψ hplus' hAplus hBplus hP
      hP').hom.toHom =
      ({ base := spaComapTopHom φ hφ hplus
         c := (presentationLimitPresheafIsoPushforward (P := P) (P' := P') φ hφ hplus ψ hψ hψφ hφψ
          hplus').hom } :
        (presentationLimitPreAdicSpace P' Bplus hBplus hP').toPresheafedSpace ⟶
          (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace) :=
  (rfl)

end Iso

end TauCeti.ValuationSpectrum

end
