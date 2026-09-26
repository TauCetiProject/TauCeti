/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
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
  obtain ⟨T', s', hT', hVeq⟩ := mem_spaRationalFamily_iff.mp (mem_spaRationalOpens.mp hV)
  let p : Presentation P := ⟨T, s, hasDenominatorPower_of_isOpen_span P T s _ hT⟩
  let q : Presentation P := ⟨T', s', hasDenominatorPower_of_isOpen_span P T' s' _ hT'⟩
  refine ⟨p.commonRefinement q, ?_, ?_, Presentation.le_def.mp (p.le_commonRefinement_left q)⟩
  · classical
    rw [Presentation.commonRefinement_num]
    exact P.isOpen_span_insert_mul_insert hT hT'
  · have hVq : V = spaBasicOpen Aplus q.num q.den :=
      Opens.ext (hVeq.trans (Set.ext fun _ ↦ mem_spaBasicOpen).symm)
    rw [spaBasicOpen_commonRefinement, ← hVq]
    exact (inf_eq_right.mpr hVW).symm

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
  have hopen := isOpen_map_algebraMap_locTopology P T s S hden hp
  rw [← locUniformSpace_toTopologicalSpace P T s S hden] at hopen
  rw [coe_locPresentation_num, ← Ideal.map_span, hρ, ← Ideal.map_map]
  exact isOpen_map_coeRingHom hopen

-- `A_U⁺` consists of power-bounded elements when `A⁺` does.
private theorem isPowerBounded_of_mem_completedPlusSubring
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ ⦃b⦄, b ∈ completedPlusSubring P Aplus T s S hden → IsPowerBounded b := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_completion_locTopology P T s S hden
  exact fun _ hb ↦ mem_powerBoundedSubring.mp
    (completedPlusSubring_le_powerBoundedSubring P Aplus hAplus T s S hden hb)

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
        (isPowerBounded_of_mem_completedPlusSubring P Aplus T s S hden hAplus) hB := by
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

-- A transport between presentation limits along an equality of opens is a restriction map.
private theorem eqToHom_presentationLimit {R : Type v} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {Q : PairOfDefinition R} {Rplus : Subring R} {V W : Opens ↥(spa Rplus)}
    (e : V = W) (e' : presentationLimit (P := Q) Rplus V = presentationLimit (P := Q) Rplus W) :
    eqToHom e' = presentationLimitMap (P := Q) e.ge := by
  subst e
  simp

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
      (isPowerBounded_of_mem_completedPlusSubring P Aplus T s S hden hAplus) _
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
    (isPowerBounded_of_mem_completedPlusSubring P Aplus T s S hden hAplus) _ _
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

end TauCeti.ValuationSpectrum
