/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# Base change of completed rational localisations along a ring homomorphism

Let `φ : A → B` be a continuous ring homomorphism of topological rings with pairs of definition
`P` and `P'`. For a presentation `p = (T, s)` of `A` and a presentation `q` of `B` with
denominator `φ(s)` whose numerators contain `φ(T)`, the universal property of `A⟨T/s⟩`
(Wedhorn, Proposition and Definition 5.51) extends `φ` uniquely to a continuous ring homomorphism

```text
A⟨T/s⟩ → B⟨q⟩
```

compatible with the structure maps. This file packages that homomorphism as a morphism
`Presentation.mapHom` of `CompleteSeparatedTopCommRingCat`, together with the extensionality
principle for morphisms out of `A⟨p⟩` and the compatibility of the structure maps with the
restriction and comparison morphisms between completed rational localisations.

When `φ` carries open ideals to open ideals and `A⁺` into `B⁺`, the preimage of the rational
subset `R(T/s)` of `Spa(A, A⁺)` under the induced map `Spa(B, B⁺) → Spa(A, A⁺)` is the rational
subset `R(φ(T)/φ(s))` of `Spa(B, B⁺)` (Wedhorn, Lemma 7.46(3)). `PresentationIndex.map` records
this at the level of the indices of the presentation limits: an admissible presentation refining
an open `U` of `Spa(A, A⁺)` induces an admissible presentation refining any open of `Spa(B, B⁺)`
containing the preimage of `U`. These are the components from which morphisms between the
structure presheaves of `Spa(A, A⁺)` and `Spa(B, B⁺)` are assembled, in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport` for isomorphisms and
completions and in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Comap` for a
general `φ` with sheafy target.

## Main definitions

* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocTopHom`: the structure map
  `A → A⟨p⟩` as a morphism of `TopCommRingCat`.
* `TauCeti.Huber.PairOfDefinition.Presentation.mapHom`: the base change `A⟨p⟩ ⟶ B⟨q⟩` of `φ`.
* `TauCeti.ValuationSpectrum.PresentationIndex.map`: the index of `Spa(B, B⁺)` induced by an
  index of `Spa(A, A⁺)`.

## Main results

* `TauCeti.Huber.PairOfDefinition.Presentation.hom_ext`: morphisms out of `A⟨p⟩` are determined by
  their composites with the structure map.
* `TauCeti.Huber.PairOfDefinition.Presentation.toCompletionLocTopHom_comp_mapHom`: the base change
  is compatible with the structure maps.
* `TauCeti.ValuationSpectrum.spaBasicOpen_map_pres`: the rational open presented by the induced
  index is the preimage of the rational open presented by the original index.
* `TauCeti.ValuationSpectrum.presentationLimitπToPresentation_comp_eq`: two projections of a
  presentation limit followed by morphisms agreeing on `A` agree.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and Definition 5.51,
  Lemma 7.46 and §8.1.
-/

open CategoryTheory _root_.TopologicalSpace

public section

universe v

namespace TauCeti.Huber.PairOfDefinition

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B}

/-! ### The structure map, and maps out of `A⟨p⟩` -/

/-- The structure map `A → A⟨p⟩`, as a morphism of `TopCommRingCat`. -/
noncomputable def Presentation.toCompletionLocTopHom (p : Presentation P) :
    TopCommRingCat.of A ⟶ p.completionLocObj.obj := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  exact (⟨toCompletionLoc P p.num p.den _ p.hasDenominatorPower,
      continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩ :
      TopCommRingCat.of A ⟶
        TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den))) ≫
    eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm

/-- The defining equation of `Presentation.toCompletionLocTopHom`: the structure map
`toCompletionLoc`, transported across `completionLocObj_obj`. -/
theorem Presentation.toCompletionLocTopHom_eq (p : Presentation P) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    p.toCompletionLocTopHom = (⟨toCompletionLoc P p.num p.den _ p.hasDenominatorPower,
        continuous_toCompletionLoc P p.num p.den _ p.hasDenominatorPower⟩ :
        TopCommRingCat.of A ⟶
          TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den))) ≫
      eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm :=
  (rfl)

/-- Morphisms out of `A⟨p⟩` are determined by their composites with the structure map. -/
theorem Presentation.hom_ext (p : Presentation P) {X : CompleteSeparatedTopCommRingCat.{v}}
    {f g : p.completionLocObj ⟶ X}
    (h : p.toCompletionLocTopHom ≫ f.hom = p.toCompletionLocTopHom ≫ g.hom) : f = g := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  apply InducedCategory.hom_ext
  -- as maps out of the completion itself, `f` and `g` agree by extensionality for `A⟨p⟩`
  rw [← cancel_epi (eqToHom (completionLocObj_obj P p.num p.den _ p.hasDenominatorPower).symm)]
  refine Subtype.ext <| completion_locTopology_ringHom_ext_of_continuous P p.num p.den _
    p.hasDenominatorPower _ _ (_ ≫ f.hom).2 (_ ≫ g.hom).2 ?_
  simp only [Presentation.toCompletionLocTopHom, Category.assoc] at h
  exact congrArg Subtype.val h

/-- Restriction morphisms commute with the structure maps. -/
@[reassoc]
theorem Presentation.toCompletionLocTopHom_comp_restrictionHom {p q : Presentation P}
    (h : p ≤ q) :
    p.toCompletionLocTopHom ≫ (Presentation.restrictionHom h).hom = q.toCompletionLocTopHom := by
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  rw [Presentation.restrictionHom_eq h r hr hT, restrictionObjHom_eq_completionLocObjHom,
    completionLocObjHom_hom]
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  simp only [Presentation.toCompletionLocTopHom, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  apply eq_whisker
  exact Subtype.ext (restrictionRingHom_comp_toCompletionLoc P _ _ _ _ _ _ _ _ r hr hT)

/-- The structure map is compatible with the transport along an equality of presentations. -/
@[reassoc]
theorem Presentation.toCompletionLocTopHom_comp_eqToHom_hom {p q : Presentation P} (e : p = q) :
    p.toCompletionLocTopHom ≫ (eqToHom (congrArg Presentation.completionLocObj e)).hom =
      q.toCompletionLocTopHom := by
  subst e
  simp

/-- **Base change of `A⟨T/s⟩`.** A continuous ring homomorphism `φ : A →+* B` extends uniquely to
a continuous map `A⟨p⟩ → B⟨q⟩` compatible with the structure maps, when `q` has denominator
`φ p.den` and contains the images of the numerators of `p`. -/
private theorem existsUnique_continuous_ringHom_comp_eq (φ : A →+* B) (hφ : Continuous φ)
    (p : Presentation P) (q : Presentation P') (hden : q.den = φ p.den)
    (hnum : ∀ t ∈ p.num, φ t ∈ q.num) :
    letI := locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
    letI := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    letI := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
    ∃! g : UniformSpace.Completion (Localization.Away p.den) →+*
        UniformSpace.Completion (Localization.Away q.den),
      Continuous g ∧ g.comp (toCompletionLoc P p.num p.den _ p.hasDenominatorPower) =
        (toCompletionLoc P' q.num q.den _ q.hasDenominatorPower).comp φ := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isHuberRing_completion_locTopology P' q.num q.den _ q.hasDenominatorPower
  have hq : q.den = φ p.den * 1 := by rw [hden, mul_one]
  have hu := isUnit_toCompletionLoc_of_dvd P' q.num q.den _ q.hasDenominatorPower ⟨1, hq⟩
  exact existsUnique_continuous_ringHom_completion_locTopology P p.num p.den _
    p.hasDenominatorPower ((continuous_toCompletionLoc P' _ _ _ _).comp hφ).continuousAt hu
    fun t ht ↦ isPowerBounded_toCompletionLoc_mul_unit_inv P' _ _ _ _ hq hu
      ((mul_one (φ t)).symm ▸ hnum t ht)

/-- The morphism `A⟨p⟩ ⟶ B⟨q⟩` of `existsUnique_continuous_ringHom_comp_eq`. -/
noncomputable def Presentation.mapHom (φ : A →+* B) (hφ : Continuous φ) (p : Presentation P)
    (q : Presentation P') (hden : q.den = φ p.den) (hnum : ∀ t ∈ p.num, φ t ∈ q.num) :
    p.completionLocObj ⟶ q.completionLocObj := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  let _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have hg := existsUnique_continuous_ringHom_comp_eq φ hφ p q hden hnum
  exact InducedCategory.homMk (eqToHom (completionLocObj_obj P p.num p.den _ _) ≫
    (⟨hg.choose, hg.choose_spec.1.1⟩ :
      TopCommRingCat.of (UniformSpace.Completion (Localization.Away p.den)) ⟶
        TopCommRingCat.of (UniformSpace.Completion (Localization.Away q.den))) ≫
      eqToHom (completionLocObj_obj P' q.num q.den _ _).symm)

/-- `Presentation.mapHom` carries the structure map of `p` to that of `q` after `φ`. -/
@[reassoc]
theorem Presentation.toCompletionLocTopHom_comp_mapHom (φ : A →+* B) (hφ : Continuous φ)
    (p : Presentation P) (q : Presentation P') (hden : q.den = φ p.den)
    (hnum : ∀ t ∈ p.num, φ t ∈ q.num) :
    p.toCompletionLocTopHom ≫ (p.mapHom φ hφ q hden hnum).hom =
      (⟨φ, hφ⟩ : TopCommRingCat.of A ⟶ TopCommRingCat.of B) ≫ q.toCompletionLocTopHom := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P' q.num q.den _ q.hasDenominatorPower
  simp only [Presentation.toCompletionLocTopHom, Presentation.mapHom, InducedCategory.homMk_hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  apply eq_whisker
  exact Subtype.ext (existsUnique_continuous_ringHom_comp_eq φ hφ p q hden hnum).choose_spec.1.2

end TauCeti.Huber.PairOfDefinition

namespace TauCeti.ValuationSpectrum

open CategoryTheory.Limits TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A B : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {P : PairOfDefinition A}
  {P' : PairOfDefinition B} {Aplus : Subring A} {Bplus : Subring B}

/-! ### Transporting presentations -/

variable (φ : A →+* B) (hφ : Continuous φ)
  (hopen : ∀ ⦃J : Ideal A⦄, IsOpen (J : Set A) → IsOpen (J.map φ : Set B))

include hopen in
open scoped Classical in
/-- The image under `φ` of an index of `U`, as an index of any `V` containing the preimage of `U`
under the induced map of adic spectra: its presentation is `(φ(T), φ(s))` for the presentation
`(T, s)` of the index. -/
noncomputable def PresentationIndex.map (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus)
    {U : Opens ↥(spa Aplus)} {V : Opens ↥(spa Bplus)}
    (hUV : ∀ w, spaComap φ hφ Aplus Bplus hplus w ∈ U → w ∈ V)
    (i : PresentationIndex (P := P) Aplus U) : PresentationIndex (P := P') Bplus V where
  pres := ⟨i.pres.num.image φ, φ i.pres.den, hasDenominatorPower_of_isOpen_span P' _ _ _ (by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hopen i.isOpen_span)⟩
  isOpen_span := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hopen i.isOpen_span
  le_open w hw := hUV w <| i.le_open <| mem_spaBasicOpen.mpr <|
    (Set.ext_iff.mp (spaComap_preimage_rationalSubset φ hφ Aplus Bplus hplus
      i.pres.num i.pres.den) w).mpr (mem_spaBasicOpen.mp hw)

variable (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) {U : Opens ↥(spa Aplus)} {V : Opens ↥(spa Bplus)}
  (hUV : ∀ w, spaComap φ hφ Aplus Bplus hplus w ∈ U → w ∈ V)

omit [IsTopologicalRing A] in
open scoped Classical in
/-- The numerators of the induced index are the images of the numerators. -/
@[simp]
theorem PresentationIndex.map_pres_num (i : PresentationIndex (P := P) Aplus U) :
    (i.map (P' := P') φ hφ hopen hplus hUV).pres.num = i.pres.num.image φ := (rfl)

omit [IsTopologicalRing A] in
/-- The denominator of the induced index is the image of the denominator. -/
@[simp]
theorem PresentationIndex.map_pres_den (i : PresentationIndex (P := P) Aplus U) :
    (i.map (P' := P') φ hφ hopen hplus hUV).pres.den = φ i.pres.den := (rfl)

omit [IsTopologicalRing A] in
open scoped Classical in
/-- **The induced index presents the preimage**: the rational open `R(φ(T)/φ(s))` presented by the
induced index is the preimage of the rational open `R(T/s)` presented by the original index under
the induced map of adic spectra. -/
theorem PresentationIndex.spaBasicOpen_map_pres (i : PresentationIndex (P := P) Aplus U) :
    spaBasicOpen Bplus (i.map (P' := P') φ hφ hopen hplus hUV).pres.num
        (i.map (P' := P') φ hφ hopen hplus hUV).pres.den =
      (Opens.map (spaComapTopHom φ hφ hplus)).obj (spaBasicOpen Aplus i.pres.num i.pres.den) := by
  rw [map_spaComapTopHom_obj_spaBasicOpen φ hφ hplus, map_pres_num, map_pres_den]

omit [IsTopologicalRing A] in
/-- `PresentationIndex.map` preserves refinement. -/
theorem PresentationIndex.map_mono {i j : PresentationIndex (P := P) Aplus U} (h : i ≤ j) :
    i.map (P' := P') φ hφ hopen hplus hUV ≤ j.map φ hφ hopen hplus hUV := by
  classical
  obtain ⟨r, hr, hT⟩ := Presentation.le_def.mp h
  refine Presentation.le_def.mpr ⟨φ r, ?_, fun t ht ↦ ?_⟩
  · rw [map_pres_den, map_pres_den, hr, map_mul]
  · rw [map_pres_num] at ht ⊢
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image.mpr ⟨a * r, hT a ha, map_mul φ a r⟩

/-! ### The comparison maps of presentation limits -/

/-- Two projections of `presentationLimit` followed by maps agreeing on `A` agree, when the first
index is refined by the second. -/
theorem presentationLimitπToPresentation_comp_eq {W : Opens ↥(spa Aplus)}
    {X : CompleteSeparatedTopCommRingCat.{v}} {k₁ k₂ : PresentationIndex (P := P) Aplus W}
    (hk : k₁ ≤ k₂) {f₁ : k₁.pres.completionLocObj ⟶ X} {f₂ : k₂.pres.completionLocObj ⟶ X}
    (hf : k₁.pres.toCompletionLocTopHom ≫ f₁.hom = k₂.pres.toCompletionLocTopHom ≫ f₂.hom) :
    presentationLimitπToPresentation Aplus W k₁ ≫ f₁ =
      presentationLimitπToPresentation Aplus W k₂ ≫ f₂ := by
  rw [← presentationLimitπ_comp_restriction hk, Category.assoc]
  refine congrArg _ (k₁.pres.hom_ext ?_)
  rw [ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_restrictionHom_assoc, hf]

/-- The comparison morphism of a containment of rational subsets commutes with the structure
maps. -/
@[reassoc]
theorem toCompletionLocTopHom_comp_homOfRationalSubsetSubset
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {p q : Presentation P}
    (h : rationalSubset Aplus q.num q.den ⊆ rationalSubset Aplus p.num p.den) :
    p.toCompletionLocTopHom ≫ (homOfRationalSubsetSubset Aplus hAplus h).hom =
      q.toCompletionLocTopHom := by
  -- through the common refinement `k` of `p` and `q`, which presents `R(q)`: the comparison
  -- morphism is restriction to `k` followed by the inverse of the restriction from `q` to `k`
  have hpk := p.le_commonRefinement_left q
  have hqk := p.le_commonRefinement_right q
  have hqR : rationalSubset Aplus q.num q.den ⊆
      rationalSubset Aplus (p.commonRefinement q).num (p.commonRefinement q).den := by
    rw [rationalSubset_commonRefinement]
    exact Set.subset_inter h subset_rfl
  have e₁ : homOfRationalSubsetSubset Aplus hAplus h =
      Presentation.restrictionHom hpk ≫ homOfRationalSubsetSubset Aplus hAplus hqR := by
    rw [restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus hpk,
      homOfRationalSubsetSubset_comp]
  have e₂ : Presentation.restrictionHom hqk ≫ homOfRationalSubsetSubset Aplus hAplus hqR = 𝟙 _ := by
    rw [restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus hqk,
      homOfRationalSubsetSubset_comp,
      homOfRationalSubsetSubset_self]
  rw [e₁, ObjectProperty.FullSubcategory.comp_hom,
    Presentation.toCompletionLocTopHom_comp_restrictionHom_assoc,
    ← Presentation.toCompletionLocTopHom_comp_restrictionHom hqk, Category.assoc,
    ← ObjectProperty.FullSubcategory.comp_hom, e₂, ObjectProperty.FullSubcategory.id_hom,
    Category.comp_id]

/-- Two projections of `presentationLimit` followed by maps agreeing on `A` agree, when the
rational subset of the first index lies in that of the second and `A⁺` consists of power-bounded
elements. -/
theorem presentationLimitπToPresentation_comp_eq_of_subset
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {W : Opens ↥(spa Aplus)}
    {X : CompleteSeparatedTopCommRingCat.{v}} {k₁ k₂ : PresentationIndex (P := P) Aplus W}
    (hk : rationalSubset Aplus k₁.pres.num k₁.pres.den ⊆
      rationalSubset Aplus k₂.pres.num k₂.pres.den)
    {f₁ : k₁.pres.completionLocObj ⟶ X} {f₂ : k₂.pres.completionLocObj ⟶ X}
    (hf : k₁.pres.toCompletionLocTopHom ≫ f₁.hom = k₂.pres.toCompletionLocTopHom ≫ f₂.hom) :
    presentationLimitπToPresentation Aplus W k₁ ≫ f₁ =
      presentationLimitπToPresentation Aplus W k₂ ≫ f₂ := by
  rw [presentationLimitπ_eq_π_comp hAplus k₂ k₁ hk, Category.assoc]
  refine congrArg _ (k₂.pres.hom_ext ?_)
  rw [ObjectProperty.FullSubcategory.comp_hom,
    toCompletionLocTopHom_comp_homOfRationalSubsetSubset_assoc, hf]

end TauCeti.ValuationSpectrum

end
