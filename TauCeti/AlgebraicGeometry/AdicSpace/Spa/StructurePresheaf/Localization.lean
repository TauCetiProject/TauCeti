/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Point
public import TauCeti.RingTheory.Huber.LocalizationTopology.Iterated

/-!
# The presentation limit on a rational subset of a rational localisation

Let `U = R(T/s)` be a rational subset of `Spa(A, A⁺)`, let `B = A⟨T/s⟩` with structure map
`ρ : A → B` and plus ring `A_U⁺`, and let `j : Spa(B, A_U⁺) → Spa(A, A⁺)` be induced by `ρ`.
Wedhorn's Remark 8.4 identifies `𝒪_X(V)` with `𝒪_U(j⁻¹(V))` for every rational `V ⊆ U`, compatibly
with restriction. This file proves that statement for `presentationLimit`, the limit indexed by
admissible presentations, when `A⁺` consists of power-bounded elements.

## Main definitions

* `TauCeti.ValuationSpectrum.presentationLimitLocIso` : the isomorphism
  `presentationLimit Aplus V ≅ presentationLimit A_U⁺ j⁻¹(V)` for a rational `V ⊆ R(T/s)`, where
  `j⁻¹(V)` is `TauCeti.ValuationSpectrum.locOpensComap`.

## Main results

* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_presentationLimitLocIso_hom` : these
  isomorphisms commute with the restriction maps.
* `TauCeti.ValuationSpectrum.presentationLimitLocIso_hom_presentationLimitMap_apply` and
  `TauCeti.ValuationSpectrum.bijective_presentationLimitLocIso_hom` : the same, and bijectivity,
  read on sections.
* `TauCeti.ValuationSpectrum.comap_presentationLimitLocIso_rationalLocalizationPoint` : read on
  rational coordinate rings, these isomorphisms match the points determined by `y` and by `j(y)`.
  This is what makes the stalk valuations compatible with Remark 8.4.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.4 and
  Proposition 8.2.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (T : Finset A) (s : A)
  (S : Type v) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
  (hden : HasDenominatorPower P T s S)

/-! ### A presentation of `V` refining `(T, s)` -/

-- A rational `V ⊆ R(T/s)` is presented by the common refinement of `(T, s)` with any admissible
-- presentation of `V`; the common refinement refines `(T, s)` with cofactor that presentation's
-- denominator.
private theorem exists_presentation_refining (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    {V : Opens ↥(spa Aplus)} (hV : V ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) :
    ∃ p : Presentation P, IsOpen (Ideal.span (p.num : Set A) : Set A) ∧
      V = spaBasicOpen Aplus p.num p.den ∧ ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num := by
  obtain ⟨T', s', hT', rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  let p : Presentation P := ⟨T, s, hasDenominatorPower_of_isOpen_span P T s _ hT⟩
  let q : Presentation P := ⟨T', s', hasDenominatorPower_of_isOpen_span P T' s' _ hT'⟩
  refine ⟨p.commonRefinement q, ?_,
    ((spaBasicOpen_commonRefinement Aplus p q).trans (inf_eq_right.mpr hVW)).symm,
    Presentation.le_def.mp (p.le_commonRefinement_left q)⟩
  classical
  rw [Presentation.commonRefinement_num]
  exact P.isOpen_span_insert_mul_insert hT hT'

/-! ### The presentation over `A⟨T/s⟩` -/

open scoped Classical in
-- The presentation `(ρ(T''), ρ(s''))` of a rational subset of `Spa (A⟨T/s⟩, A_U⁺)`, where
-- `ρ : A → A⟨T/s⟩` is the structure map and `(T'', s'')` is a presentation over `A`.
private noncomputable abbrev locPresentation (p : Presentation P) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Presentation (completionLocalization P T s S hden) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  ⟨p.num.image (toCompletionLoc P T s S hden), toCompletionLoc P T s S hden p.den,
    hasDenominatorPower_completionLocalization_of_coe_eq_image P T s S hden p.num p.den _
      p.hasDenominatorPower _ _ Finset.coe_image⟩

open scoped Classical in
-- The numerators of `locPresentation` are the images of the numerators over `A`.
private theorem coe_locPresentation_num (p : Presentation P) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ((locPresentation P T s S hden p).num : Set (UniformSpace.Completion S)) =
      toCompletionLoc P T s S hden '' p.num :=
  Finset.coe_image

-- The numerators `ρ(T'')` span an open ideal when `T''` does: the ideal is carried to an open
-- ideal by the localisation map and then by the completion map.
private theorem isOpen_span_locPresentation_num {p : Presentation P}
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    IsOpen (Ideal.span ((locPresentation P T s S hden p).num : Set (UniformSpace.Completion S)) :
      Set (UniformSpace.Completion S)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  have hρ : toCompletionLoc P T s S hden =
      UniformSpace.Completion.coeRingHom.comp (algebraMap A S) :=
    RingHom.ext (toCompletionLoc_apply P T s S hden)
  have hopen := isOpen_map_algebraMap_locUniformSpace P T s S hden hp
  rw [coe_locPresentation_num, ← Ideal.map_span, hρ, ← Ideal.map_map]
  exact isOpen_map_coeRingHom hopen

/-! ### The ring isomorphism as an isomorphism of objects -/

-- Wedhorn's Remark 8.4 for rings, `A⟨T''/s''⟩ ≅ A⟨T/s⟩⟨ρ(T'')/ρ(s'')⟩`, as an isomorphism in
-- `CompleteSeparatedTopCommRingCat`.
private noncomputable def locPresentationIso {p : Presentation P}
    (hle : ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    p.completionLocObj ≅ (locPresentation P T s S hden p).completionLocObj := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let q := locPresentation P T s S hden p
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  let e := iteratedLocalizationRingEquiv P T s S hden p.num p.den _ p.hasDenominatorPower
    (Localization.Away q.den) q.num (coe_locPresentation_num P T s S hden p) hle.choose
    hle.choose_spec.1 hle.choose_spec.2
  let f : TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) ≅
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den)) :=
    { hom := ⟨e, continuous_iteratedLocalizationRingEquiv ..⟩
      inv := ⟨e.symm, continuous_iteratedLocalizationRingEquiv_symm ..⟩
      hom_inv_id := Subtype.ext (RingHom.ext e.symm_apply_apply)
      inv_hom_id := Subtype.ext (RingHom.ext e.apply_symm_apply) }
  exact ObjectProperty.isoMk _ (eqToIso (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower)
    ≪≫ f ≪≫ eqToIso (completionLocObj_obj _ q.num q.den _ q.hasDenominatorPower).symm)

-- Under the identifications with the underlying rings, the isomorphism is the ring isomorphism.
private theorem map_locPresentationIso_hom {p : Presentation P}
    (hle : ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace _ _ _ _ (locPresentation P T s S hden p).hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace _ _ _ _
      (locPresentation P T s S hden p).hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace _ _ _ _
      (locPresentation P T s S hden p).hasDenominatorPower
    (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
        (locPresentationIso P T s S hden hle).hom ≫
        (locPresentation P T s S hden p).completionLocObjCommRingCatIso.hom =
      p.completionLocObjCommRingCatIso.hom ≫
        CommRingCat.ofHom (iteratedLocalizationRingEquiv P T s S hden p.num p.den _
          p.hasDenominatorPower (Localization.Away (locPresentation P T s S hden p).den)
          (locPresentation P T s S hden p).num (coe_locPresentation_num P T s S hden p)
          hle.choose hle.choose_spec.1 hle.choose_spec.2 : _ →+* _) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  rw [locPresentationIso, Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.isoMk_hom,
    Presentation.completionLocObjCommRingCatIso_hom,
    Presentation.completionLocObjCommRingCatIso_hom]
  exact TauCeti.TopCommRingCat.forget₂_map_eqToHom_comp_comp_eqToHom _ _ _ _

-- **The ring-level square.** Comparison maps over `A` and over `A⟨T/s⟩` correspond under the
-- isomorphisms: both composites are continuous and restrict to the same map on `A`.
private theorem homOfRationalSubsetSubset_comp_locPresentationIso_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p p' : Presentation P}
    (hle : ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num)
    (hle' : ∃ r, p'.den = s * r ∧ ∀ t ∈ T, t * r ∈ p'.num)
    (h : rationalSubset Aplus p'.num p'.den ⊆ rationalSubset Aplus p.num p.den)
    (hB : letI := locUniformSpace P T s S hden
      letI := isUniformAddGroup_locUniformSpace P T s S hden
      letI := isTopologicalRing_locUniformSpace P T s S hden
      rationalSubset (completedPlusSubring P Aplus T s S hden)
          (locPresentation P T s S hden p').num (locPresentation P T s S hden p').den ⊆
        rationalSubset (completedPlusSubring P Aplus T s S hden)
          (locPresentation P T s S hden p).num (locPresentation P T s S hden p).den) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    homOfRationalSubsetSubset Aplus hAplus h ≫ (locPresentationIso P T s S hden hle').hom =
      (locPresentationIso P T s S hden hle).hom ≫ homOfRationalSubsetSubset _
        (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) hB := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let q' := locPresentation P T s S hden p'
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace _ q'.num q'.den _ q'.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace _ q'.num q'.den _ q'.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace _ q'.num q'.den _ q'.hasDenominatorPower
  apply (TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map_injective
  rw [← cancel_mono q'.completionLocObjCommRingCatIso.hom, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, map_locPresentationIso_hom P T s S hden hle',
    map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom]
  simp only [← Category.assoc, map_locPresentationIso_hom P T s S hden hle,
    map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom]
  simp only [Category.assoc, ← CommRingCat.ofHom_comp]
  refine congrArg (_ ≫ ·) (congrArg CommRingCat.ofHom ?_)
  refine completion_locTopology_ringHom_ext_of_continuous P p.num p.den _ p.hasDenominatorPower
    _ _ ((continuous_iteratedLocalizationRingEquiv ..).comp
      (continuous_ringHomOfRationalSubsetSubset ..))
    ((continuous_ringHomOfRationalSubsetSubset ..).comp
      (continuous_iteratedLocalizationRingEquiv ..)) ?_
  rw [RingHom.comp_assoc, RingHom.comp_assoc, ringHomOfRationalSubsetSubset_comp_toCompletionLoc,
    iteratedLocalizationRingEquiv_coe_comp_toCompletionLoc,
    iteratedLocalizationRingEquiv_coe_comp_toCompletionLoc, ← RingHom.comp_assoc,
    ringHomOfRationalSubsetSubset_comp_toCompletionLoc]

/-! ### The isomorphism for a chosen presentation -/

-- The isomorphism of Remark 8.4 computed through a presentation `p` of `V` that refines `(T, s)`:
-- `𝒪_X(V) ≅ A⟨p⟩ ≅ A⟨T/s⟩⟨ρ(p)⟩ ≅ 𝒪_U(j⁻¹V)`.
private noncomputable def presentationLimitLocIsoAux (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    {p : Presentation P} {V : Opens ↥(spa Aplus)}
    (hpV : IsOpen (Ideal.span (p.num : Set A) : Set A) ∧ V = spaBasicOpen Aplus p.num p.den ∧
      ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    presentationLimit (P := P) Aplus V ≅
      presentationLimit (P := completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden) (locOpensComap P Aplus T s S hden V) :=
  letI := locUniformSpace P T s S hden
  letI := isUniformAddGroup_locUniformSpace P T s S hden
  letI := isTopologicalRing_locUniformSpace P T s S hden
  eqToIso (congrArg (presentationLimit (P := P) Aplus) hpV.2.1) ≪≫
    presentationLimitRationalIso Aplus hAplus p hpV.1 ≪≫ locPresentationIso P T s S hden hpV.2.2 ≪≫
    (presentationLimitRationalIso _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) _
      (isOpen_span_locPresentation_num P T s S hden hpV.1)).symm ≪≫
    eqToIso (congrArg (presentationLimit (P := completionLocalization P T s S hden)
      (completedPlusSubring P Aplus T s S hden))
      ((locOpensComap_spaBasicOpen P Aplus T s S hden p.num p.den).symm.trans
        (congrArg _ hpV.2.1.symm)))

-- Naturality of the isomorphism computed through presentations, for any choice of presentations.
private theorem presentationLimitMap_comp_presentationLimitLocIsoAux_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p p' : Presentation P}
    {V V' : Opens ↥(spa Aplus)} (hpV : IsOpen (Ideal.span (p.num : Set A) : Set A) ∧
      V = spaBasicOpen Aplus p.num p.den ∧ ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num)
    (hpV' : IsOpen (Ideal.span (p'.num : Set A) : Set A) ∧ V' = spaBasicOpen Aplus p'.num p'.den ∧
      ∃ r, p'.den = s * r ∧ ∀ t ∈ T, t * r ∈ p'.num) (h : V' ≤ V) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    presentationLimitMap (P := P) h ≫
        (presentationLimitLocIsoAux P Aplus T s S hden hAplus hpV').hom =
      (presentationLimitLocIsoAux P Aplus T s S hden hAplus hpV).hom ≫
        presentationLimitMap (P := completionLocalization P T s S hden)
          (locOpensComap_mono P Aplus T s S hden h) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  obtain ⟨hp, rfl, hle⟩ := hpV
  obtain ⟨hp', rfl, hle'⟩ := hpV'
  have hB : spaBasicOpen (completedPlusSubring P Aplus T s S hden)
      (locPresentation P T s S hden p').num (locPresentation P T s S hden p').den ≤
      spaBasicOpen _ (locPresentation P T s S hden p).num (locPresentation P T s S hden p).den := by
    rw [← locOpensComap_spaBasicOpen, ← locOpensComap_spaBasicOpen]
    exact locOpensComap_mono P Aplus T s S hden h
  have hX := presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p p' hp hp' h
  have hY := presentationLimitRationalIso_inv_comp_map_comp_hom _
    (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) _ _
    (isOpen_span_locPresentation_num P T s S hden hp)
    (isOpen_span_locPresentation_num P T s S hden hp') hB
  rw [Iso.inv_comp_eq] at hX
  rw [← Category.assoc, ← Iso.eq_comp_inv] at hY
  simp only [presentationLimitLocIsoAux, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.assoc]
  rw [eqToHom_presentationLimit (locOpensComap_spaBasicOpen P Aplus T s S hden p'.num p'.den).symm,
    eqToHom_presentationLimit (locOpensComap_spaBasicOpen P Aplus T s S hden p.num p.den).symm,
    reassoc_of% hX, reassoc_of% homOfRationalSubsetSubset_comp_locPresentationIso_hom P Aplus T s S
    hden hAplus hle hle' _ (spaBasicOpen_le_spaBasicOpen_iff.mp hB), ← reassoc_of% hY,
    presentationLimitMap_comp, presentationLimitMap_comp]

/-! ### Wedhorn's Remark 8.4 -/

/-- **Wedhorn's Remark 8.4, for the presentation limit.** Let `B = A⟨T/s⟩` with plus ring `A_U⁺`,
where `T` spans an open ideal and `A⁺` consists of power-bounded elements. For a rational open
`V ⊆ R(T/s)` of `Spa(A, A⁺)`, the limit over the presentations inside `V` is isomorphic to the
limit, over `B`, of the presentations inside the pullback `locOpensComap P Aplus T s S hden V`.

It commutes with the restriction maps: `presentationLimitMap_comp_presentationLimitLocIso_hom`.
-/
noncomputable def presentationLimitLocIso (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (V : Opens ↥(spa Aplus))
    (hV : V ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    presentationLimit (P := P) Aplus V ≅
      presentationLimit (P := completionLocalization P T s S hden)
        (completedPlusSubring P Aplus T s S hden) (locOpensComap P Aplus T s S hden V) :=
  presentationLimitLocIsoAux P Aplus T s S hden hAplus
    (exists_presentation_refining P Aplus T s hT hV hVW).choose_spec

/-- **Transport of `presentationLimitLocIso` along an equality of rational opens**: the
isomorphisms at two equal opens `V = V'` agree up to the transports of the two presentation limits
along that equality. -/
theorem presentationLimitLocIso_hom_congr (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) {V V' : Opens ↥(spa Aplus)} (e : V = V')
    (hV : V ∈ spaRationalOpens Aplus) (hV' : V' ∈ spaRationalOpens Aplus)
    (hVW : V ≤ spaBasicOpen Aplus T s) (hVW' : V' ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom =
      eqToHom (congrArg _ e) ≫
        (presentationLimitLocIso P Aplus T s S hden hAplus hT V' hV' hVW').hom ≫
        eqToHom (congrArg _ (congrArg (locOpensComap P Aplus T s S hden) e.symm)) := by
  subst e
  simp

/-- **Wedhorn's Remark 8.4 is natural in `V`.** For rational opens `V' ⊆ V ⊆ R(T/s)`, the
isomorphisms `presentationLimitLocIso` at `V` and at `V'` carry the restriction map of `V' ⊆ V`
over `A` to the restriction map of `locOpensComap … V' ⊆ locOpensComap … V` over `A⟨T/s⟩`. -/
theorem presentationLimitMap_comp_presentationLimitLocIso_hom
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    {V V' : Opens ↥(spa Aplus)} (hV : V ∈ spaRationalOpens Aplus)
    (hV' : V' ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) (h : V' ≤ V) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    presentationLimitMap (P := P) h ≫
        (presentationLimitLocIso P Aplus T s S hden hAplus hT V' hV' (h.trans hVW)).hom =
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom ≫
        presentationLimitMap (P := completionLocalization P T s S hden)
          (locOpensComap_mono P Aplus T s S hden h) :=
  presentationLimitMap_comp_presentationLimitLocIsoAux_hom P Aplus T s S hden hAplus _ _ h

/-- **Wedhorn's Remark 8.4 is natural in `V`, on sections.** This is
`presentationLimitMap_comp_presentationLimitLocIso_hom` evaluated at a section `x` over `V`. -/
theorem presentationLimitLocIso_hom_presentationLimitMap_apply
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    {V V' : Opens ↥(spa Aplus)} (hV : V ∈ spaRationalOpens Aplus)
    (hV' : V' ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) (h : V' ≤ V)
    (x : presentationLimit (P := P) Aplus V) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    (presentationLimitLocIso P Aplus T s S hden hAplus hT V' hV' (h.trans hVW)).hom.hom.1
        ((presentationLimitMap (P := P) h).hom.1 x) =
      (presentationLimitMap (P := completionLocalization P T s S hden)
        (locOpensComap_mono P Aplus T s S hden h)).hom.1
          ((presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom.hom.1 x) :=
  ConcreteCategory.congr_hom (presentationLimitMap_comp_presentationLimitLocIso_hom P Aplus T s S
    hden hAplus hT hV hV' hVW h) x

/-- **Wedhorn's Remark 8.4 is a bijection on sections**: `presentationLimitLocIso` at a rational
open `V ⊆ R(T/s)`, applied to sections. -/
theorem bijective_presentationLimitLocIso_hom (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) {V : Opens ↥(spa Aplus)}
    (hV : V ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Function.Bijective (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom.hom.1 :=
  ⟨Function.LeftInverse.injective
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom_inv_id_apply,
    Function.RightInverse.surjective
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).inv_hom_id_apply⟩

/-! ### The points of the rational coordinate rings -/

-- The point of `A⟨T/s⟩⟨ρ(p)⟩` determined by `y ∈ R(ρ(p))` pulls back, along the ring isomorphism
-- `A⟨p⟩ ≅ A⟨T/s⟩⟨ρ(p)⟩` of Remark 8.4, to the point of `A⟨p⟩` determined by `j(y)`: the pullback
-- is a point of `Spa (A⟨p⟩, A_p⁺)` lying over `j(y)`, and `Spa (A⟨p⟩, A_p⁺) → R(p)` is injective.
private theorem comap_locPresentationIso_rationalLocalizationPoint (hP : P.ringOfDefinition ≤ Aplus)
    {p : Presentation P} (hle : ∃ r, p.den = s * r ∧ ∀ t ∈ T, t * r ∈ p.num) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (y : spa (completedPlusSubring P Aplus T s S hden))
      (hy : y ∈ spaBasicOpen (completedPlusSubring P Aplus T s S hden)
        (locPresentation P T s S hden p).num (locPresentation P T s S hden p).den),
      comap ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          (locPresentationIso P T s S hden hle).hom).hom
        (rationalLocalizationPoint
          (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
          (locPresentation P T s S hden p) y hy) =
      rationalLocalizationPoint hP p (spaComapLoc P Aplus T s S hden y)
        (by rwa [← locOpensComap_spaBasicOpen, mem_locOpensComap] at hy) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  let q := locPresentation P T s S hden p
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace _ q.num q.den _ q.hasDenominatorPower
  intro y hy
  have hP' := completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden
  let e := iteratedLocalizationRingEquiv P T s S hden p.num p.den _ p.hasDenominatorPower
    (Localization.Away q.den) q.num (coe_locPresentation_num P T s S hden p) hle.choose
    hle.choose_spec.1 hle.choose_spec.2
  have he := iteratedLocalizationRingEquiv_coe_comp_toCompletionLoc P T s S hden p.num p.den _
    p.hasDenominatorPower (Localization.Away q.den) q.num (coe_locPresentation_num P T s S hden p)
    hle.choose hle.choose_spec.1 hle.choose_spec.2
  -- `w` is the point of `Spa (A⟨T/s⟩⟨ρ(p)⟩, ·)` over `y`
  set w := (spaCompletedLocalizationHomeomorph _ _ hP' q.num q.den _ q.hasDenominatorPower).symm
    ⟨y, mem_spaBasicOpen.mp hy⟩
  have hwy : spaComapLoc _ _ q.num q.den _ q.hasDenominatorPower w = y := by
    have h := spaCompletedLocalizationHomeomorph_apply _ _ hP' q.num q.den _
      q.hasDenominatorPower w
    have h' : spaCompletedLocalizationHomeomorph _ _ hP' q.num q.den _ q.hasDenominatorPower w =
        ⟨y, mem_spaBasicOpen.mp hy⟩ :=
      Homeomorph.apply_symm_apply _ _
    exact (spaLocToRationalSubset_val _ _ _ _ _ _ w).symm.trans
      (congrArg Subtype.val (h.symm.trans h'))
  have hw := (mem_spa_iff _ _).mp w.2
  have hjy : spaComapLoc P Aplus T s S hden y ∈ spaBasicOpen Aplus p.num p.den := by
    rwa [← locOpensComap_spaBasicOpen, mem_locOpensComap] at hy
  -- its pullback along `e` lies over `j(y)`
  have hcomap : comap ((e : _ →+* _).comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower))
      w.1 = (spaComapLoc P Aplus T s S hden y).1 := by
    rw [he, comap_comp, Function.comp_apply, ← spaComapLoc_val, hwy, spaComapLoc_val]
  have hmem : comap (e : _ →+* _) w.1 ∈
      spa (completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower) := by
    refine comap_mem_spa_completedPlusSubring P Aplus p.num p.den _ p.hasDenominatorPower _
      (continuous_iteratedLocalizationRingEquiv ..) hw.1 (fun a ha ↦ ?_) ?_
    · rw [← RingHom.comp_apply, he, RingHom.comp_apply]
      exact hw.2 _ (toCompletionLoc_mem_completedPlusSubring _ _ _ _ _ _
        (toCompletionLoc_mem_completedPlusSubring P Aplus T s S hden ha))
    · rw [hcomap]
      exact mem_spaBasicOpen.mp hjy
  -- and the point of `Spa (A⟨p⟩, A_p⁺)` over `j(y)` is unique
  have hpt : (spaCompletedLocalizationHomeomorph P Aplus hP p.num p.den _
      p.hasDenominatorPower).symm ⟨spaComapLoc P Aplus T s S hden y, mem_spaBasicOpen.mp hjy⟩ =
      ⟨comap (e : _ →+* _) w.1, hmem⟩ := by
    rw [Homeomorph.symm_apply_eq]
    refine Subtype.ext (Subtype.ext ?_)
    rw [spaCompletedLocalizationHomeomorph_apply, spaLocToRationalSubset_val, ← hcomap,
      spaComapLoc_val, comap_comp, Function.comp_apply]
  rw [rationalLocalizationPoint_def, rationalLocalizationPoint_def, comap_hom_comap_hom,
    map_locPresentationIso_hom P T s S hden hle, ← comap_hom_comap_hom, CommRingCat.hom_ofHom, hpt]

/-- **Wedhorn's Remark 8.4 matches the points of the rational coordinate rings.** Let
`V ⊆ R(T/s)` be a rational open of `Spa(A, A⁺)` presented by `p`, let `q` present its pullback
`j⁻¹(V)` to `Spa(A⟨T/s⟩, A_U⁺)`, and let `y ∈ j⁻¹(V)`. The ring map
`A⟨p⟩ ≅ 𝒪_X(V) ≅ 𝒪_U(j⁻¹(V)) ≅ A⟨T/s⟩⟨q⟩` induced by `presentationLimitLocIso` pulls the point of
`A⟨T/s⟩⟨q⟩` determined by `y` back to the point of `A⟨p⟩` determined by `j(y)`. -/
theorem comap_presentationLimitLocIso_rationalLocalizationPoint
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) {V : Opens ↥(spa Aplus)}
    (hV : V ∈ spaRationalOpens Aplus) (hVW : V ≤ spaBasicOpen Aplus T s) (p : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A)) (hpV : V = spaBasicOpen Aplus p.num p.den) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ (q : Presentation (completionLocalization P T s S hden))
      (hq : IsOpen (Ideal.span (q.num : Set (UniformSpace.Completion S)) :
        Set (UniformSpace.Completion S)))
      (hqV : locOpensComap P Aplus T s S hden V =
        spaBasicOpen (completedPlusSubring P Aplus T s S hden) q.num q.den)
      (y : spa (completedPlusSubring P Aplus T s S hden))
      (hy : y ∈ spaBasicOpen (completedPlusSubring P Aplus T s S hden) q.num q.den),
      comap ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
          ((presentationLimitRationalIso Aplus hAplus p hp).inv ≫
            presentationLimitMap (P := P) hpV.le ≫
            (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom ≫
            presentationLimitMap (P := completionLocalization P T s S hden) hqV.ge ≫
            (presentationLimitRationalIso _
              (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden) q hq).hom)).hom
        (rationalLocalizationPoint
          (completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden)
          q y hy) =
      rationalLocalizationPoint hP p (spaComapLoc P Aplus T s S hden y)
        (hpV ▸ (mem_locOpensComap P Aplus T s S hden V y).mp (hqV ▸ hy)) := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  intro q hq hqV y hy
  have hAplus' := isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s S hden
  have hP' := completionLocalization_ringOfDefinition_le_completedPlusSubring P Aplus hP T s S hden
  -- `presentationLimitLocIso` computes through a chosen presentation `p₀` of `V` refining `(T, s)`
  obtain ⟨hp₀, hpV₀, hle₀⟩ := (exists_presentation_refining P Aplus T s hT hV hVW).choose_spec
  set p₀ := (exists_presentation_refining P Aplus T s hT hV hVW).choose
  have hA : spaBasicOpen Aplus p₀.num p₀.den ≤ spaBasicOpen Aplus p.num p.den :=
    (hpV₀.symm.trans hpV).le
  have hB : spaBasicOpen (completedPlusSubring P Aplus T s S hden) q.num q.den ≤
      spaBasicOpen _ (locPresentation P T s S hden p₀).num
        (locPresentation P T s S hden p₀).den := by
    rw [← hqV, hpV₀, locOpensComap_spaBasicOpen]
  have hcomp : (presentationLimitRationalIso Aplus hAplus p hp).inv ≫
      presentationLimitMap (P := P) hpV.le ≫
      (presentationLimitLocIso P Aplus T s S hden hAplus hT V hV hVW).hom ≫
      presentationLimitMap (P := completionLocalization P T s S hden) hqV.ge ≫
      (presentationLimitRationalIso _ hAplus' q hq).hom =
      homOfRationalSubsetSubset Aplus hAplus (spaBasicOpen_le_spaBasicOpen_iff.mp hA) ≫
        (locPresentationIso P T s S hden hle₀).hom ≫
        homOfRationalSubsetSubset _ hAplus' (spaBasicOpen_le_spaBasicOpen_iff.mp hB) := by
    simp only [presentationLimitLocIso, presentationLimitLocIsoAux, Iso.trans_hom, Iso.symm_hom,
      eqToIso.hom, Category.assoc]
    rw [eqToHom_presentationLimit hpV₀, reassoc_of% presentationLimitMap_comp,
      reassoc_of% presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p p₀ hp hp₀ hA,
      eqToHom_presentationLimit ((locOpensComap_spaBasicOpen P Aplus T s S hden _ _).symm.trans
        (congrArg _ hpV₀.symm)), reassoc_of% presentationLimitMap_comp,
      presentationLimitRationalIso_inv_comp_map_comp_hom _ hAplus' _ q
        (isOpen_span_locPresentation_num P T s S hden hp₀) hq hB]
  rw [hcomp, Functor.map_comp, Functor.map_comp, ← comap_hom_comap_hom, ← comap_hom_comap_hom]
  simp only [Functor.comp_map, ObjectProperty.ι_map]
  rw [comap_homOfRationalSubsetSubset_rationalLocalizationPoint hP' hAplus' _ q hB y hy]
  simp only [← ObjectProperty.ι_map, ← Functor.comp_map]
  rw [comap_locPresentationIso_rationalLocalizationPoint P Aplus T s S hden hP hle₀ y (hB hy)]
  simp only [Functor.comp_map, ObjectProperty.ι_map]
  exact comap_homOfRationalSubsetSubset_rationalLocalizationPoint hP hAplus p p₀ hA _ _

end TauCeti.ValuationSpectrum
