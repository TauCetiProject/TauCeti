/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived
public import TauCeti.Topology.Sheaves.SupportedCohomology.Resolution
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Relative

/-!
# Supported sections as a relative cone

For a complex `K` of sheaves of modules and a closed set `S`, supported sections on
`W` embed in the relative complex of restriction from `W` to `W ∖ S`. If restriction
is degreewise surjective (for instance, if the terms of `K` are flasque), this embedding
is a quasi-isomorphism: the kernel is precisely the supported sections.

For a nonnegative flasque resolution of `F`, this gives an isomorphism from the
right derived supported sections to the homology of the native shifted mapping cone.
Combining it with the supported Ext comparison computes `H_Sⁿ(W,F)` by that cone.
The inclusion sends a supported cochain `a` to the relative pair `(a,0)`, fixing the
normalization independently of any choice of splittings of restriction.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* N. Honda, T. Izawa and T. Suwa, *Sato hyperfunctions via relative Dolbeault
  cohomology*, relative cochain convention.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex CochainComplex

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X) (W : Opens X)

section ShortComplex

variable {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) c)

/-- Supported sections, sections, and restriction to the complement, as a short complex
of complexes. -/
abbrev supportedSubmoduleSectionsShortComplex :
    ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk
    (((supportedSubmoduleSectionsι S W).mapHomologicalComplex c).app K)
    ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (S.complInclusion W).op).mapHomologicalComplex c).app K)
    (by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        supportedSubmoduleSectionsι_comp_complInclusion]
      rfl)

/-- The sequence of supported sections and restriction is short exact when restriction
onto the complement is degreewise epimorphic. -/
lemma shortExact_supportedSubmoduleSectionsShortComplex
    (hK : ∀ n, Epi ((K.X n).obj.map (S.complInclusion W).op)) :
    (supportedSubmoduleSectionsShortComplex S W K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    shortExact_supportedSubmoduleSectionsι S W (K.X n) (hK n)

/-- A map of coefficient complexes gives the corresponding diagram of section complexes. -/
def supportedSubmoduleSectionsShortComplexMap
    {L : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) c}
    (f : K ⟶ L) : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S W L where
  τ₁ := ((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex c).map f
  τ₂ := (((sheafSections _ (ModuleCat.{u} R)).obj (op W)).mapHomologicalComplex c).map f
  τ₃ := (((sheafSections _ (ModuleCat.{u} R)).obj (op (W ⊓ S.compl))).mapHomologicalComplex c).map f
  comm₁₂ := ((supportedSubmoduleSectionsι S W).mapHomologicalComplex c).naturality f
  comm₂₃ := (((sheafSections _ (ModuleCat.{u} R)).map
    (S.complInclusion W).op).mapHomologicalComplex c).naturality f

@[simp]
lemma supportedSubmoduleSectionsShortComplexMap_τ₁
    {L : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) c}
    (f : K ⟶ L) : (supportedSubmoduleSectionsShortComplexMap S W K f).τ₁ =
      ((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex c).map f := (rfl)

@[simp]
lemma supportedSubmoduleSectionsShortComplexMap_τ₂
    {L : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) c}
    (f : K ⟶ L) : (supportedSubmoduleSectionsShortComplexMap S W K f).τ₂ =
      (((sheafSections _ (ModuleCat.{u} R)).obj (op W)).mapHomologicalComplex c).map f := (rfl)

@[simp]
lemma supportedSubmoduleSectionsShortComplexMap_τ₃
    {L : HomologicalComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) c}
    (f : K ⟶ L) : (supportedSubmoduleSectionsShortComplexMap S W K f).τ₃ =
      (((sheafSections _ (ModuleCat.{u} R)).obj (op (W ⊓ S.compl))).mapHomologicalComplex
        c).map f := (rfl)

/-- Shrinking the open domain gives a diagram of section short complexes. -/
def supportedSubmoduleSectionsShortComplexRestrict {W' : Opens X} (i : W' ⟶ W) :
    supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S W' K where
  τ₁ := ((supportedSubmoduleSectionsRestrict S i).mapHomologicalComplex c).app K
  τ₂ := (((sheafSections _ (ModuleCat.{u} R)).map i.op).mapHomologicalComplex c).app K
  τ₃ := (((sheafSections _ (ModuleCat.{u} R)).map
    (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op).mapHomologicalComplex c).app K
  comm₁₂ := by
    simp only [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      supportedSubmoduleSectionsRestrict_ι]
  comm₂₃ := by
    have h : i.op ≫ (S.complInclusion W').op = (S.complInclusion W).op ≫
        (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op := Subsingleton.elim _ _
    simp only [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, ← Functor.map_comp, h]

@[simp]
lemma supportedSubmoduleSectionsShortComplexRestrict_τ₁ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSubmoduleSectionsShortComplexRestrict S W K i).τ₁ =
      ((supportedSubmoduleSectionsRestrict S i).mapHomologicalComplex c).app K := (rfl)

@[simp]
lemma supportedSubmoduleSectionsShortComplexRestrict_τ₂ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSubmoduleSectionsShortComplexRestrict S W K i).τ₂ =
      (((sheafSections _ (ModuleCat.{u} R)).map i.op).mapHomologicalComplex c).app K := (rfl)

@[simp]
lemma supportedSubmoduleSectionsShortComplexRestrict_τ₃ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSubmoduleSectionsShortComplexRestrict S W K i).τ₃ =
      (((sheafSections _ (ModuleCat.{u} R)).map
        (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op).mapHomologicalComplex c).app K := (rfl)

end ShortComplex

noncomputable section

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)

open ComplexShape (embeddingUpNat embeddingUpNat_f)

/-- Restriction of ordinary section complexes to the complement, extended by zero to
integer degrees. -/
abbrev moduleSectionsComplRestriction :=
  extendMap (supportedSubmoduleSectionsShortComplex S W K).g embeddingUpNat

/-- The cone of restriction, shifted by `-1`, on a nonnegative complex of sheaves. -/
abbrev supportedSubmoduleSectionsMappingCocone : CochainComplex (ModuleCat.{u} R) ℤ :=
  mappingCocone (moduleSectionsComplRestriction S W K)

/-- The canonical inclusion of supported cochains in the shifted restriction cone.
Its relative second coordinate is zero; no choice of extension is involved. -/
def supportedSubmoduleSectionsToMappingCocone :
    (supportedSubmoduleSectionsShortComplex S W K).X₁.extend embeddingUpNat ⟶
      supportedSubmoduleSectionsMappingCocone S W K :=
  mappingCocone.liftShortComplex
    ((supportedSubmoduleSectionsShortComplex S W K).map (embeddingUpNat.extendFunctor _))

/-- The first projection of the supported-cochain inclusion is the usual inclusion
into all cochains on `W`. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSectionsToMappingCocone_fst :
    supportedSubmoduleSectionsToMappingCocone S W K ≫
        mappingCocone.fst (moduleSectionsComplRestriction S W K) =
      extendMap (supportedSubmoduleSectionsShortComplex S W K).f embeddingUpNat :=
  mappingCocone.liftShortComplex_fst
    ((supportedSubmoduleSectionsShortComplex S W K).map (embeddingUpNat.extendFunctor _))

/-- The second projection of the supported-cochain inclusion vanishes in every degree. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSectionsToMappingCocone_f_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (supportedSubmoduleSectionsToMappingCocone S W K).f p ≫
      (mappingCocone.snd (moduleSectionsComplRestriction S W K)).v p q hpq = 0 :=
  mappingCocone.liftShortComplex_f_snd_v
    ((supportedSubmoduleSectionsShortComplex S W K).map (embeddingUpNat.extendFunctor _)) p q hpq

/-- In relative coordinates a supported cochain goes to `(a,0)`. -/
@[simp]
lemma relativeCoordinates_supportedSubmoduleSectionsToMappingCocone (p q : ℤ) (hpq : p + -1 = q)
    (a : ((supportedSubmoduleSectionsShortComplex S W K).X₁.extend embeddingUpNat).X p) :
    mappingCocone.relativeCoordinates (moduleSectionsComplRestriction S W K) p q hpq
        ((supportedSubmoduleSectionsToMappingCocone S W K).f p a) =
      ((extendMap (supportedSubmoduleSectionsShortComplex S W K).f embeddingUpNat).f p a, 0) :=
  mappingCocone.relativeCoordinates_liftShortComplex
    ((supportedSubmoduleSectionsShortComplex S W K).map (embeddingUpNat.extendFunctor _)) p q hpq a

/-- Supported cochains and the shifted restriction cone are quasi-isomorphic when restriction
onto the complement is degreewise epimorphic. -/
theorem quasiIso_supportedSubmoduleSectionsToMappingCocone
    (hK : ∀ n, Epi ((K.X n).obj.map (S.complInclusion W).op)) :
    QuasiIso (supportedSubmoduleSectionsToMappingCocone S W K) :=
  mappingCocone.quasiIso_lift_of_shortExact
    ((shortExact_supportedSubmoduleSectionsShortComplex S W K hK).extend embeddingUpNat)

/-- In each degree where the inclusion is a quasi-isomorphism, the mapping cocone computes the
homology of supported cochains. -/
def supportedSubmoduleSectionsMappingCoconeHomologyIso (n : ℕ)
    [QuasiIsoAt (supportedSubmoduleSectionsToMappingCocone S W K) (n : ℤ)] :
    (supportedSubmoduleSectionsShortComplex S W K).X₁.homology n ≅
      (supportedSubmoduleSectionsMappingCocone S W K).homology (n : ℤ) :=
  ((supportedSubmoduleSectionsShortComplex S W K).X₁.extendHomologyIso embeddingUpNat
    (embeddingUpNat_f n)).symm ≪≫
      isoOfQuasiIsoAt (supportedSubmoduleSectionsToMappingCocone S W K) (n : ℤ)

private abbrev sectionMappingCoconeFunctor :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapShortComplex ⋙
    NatTrans.mappingCoconeFunctor ShortComplex.π₂Toπ₃

variable {S' : Closeds X} {W' : Opens X}
  {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}

/-- A commutative diagram of section short complexes induces a map of relative cones.
This applies to diagrams varying the support, the open or the coefficient complex. -/
def supportedSubmoduleSectionsMappingCoconeMap
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L) :
    supportedSubmoduleSectionsMappingCocone S W K ⟶
      supportedSubmoduleSectionsMappingCocone S' W' L :=
  (sectionMappingCoconeFunctor (R := R)).map φ

/-- The first projection commutes with the map of section diagrams. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSectionsMappingCoconeMap_fst
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L) :
    supportedSubmoduleSectionsMappingCoconeMap S W K φ ≫
        mappingCocone.fst (moduleSectionsComplRestriction S' W' L) =
      mappingCocone.fst (moduleSectionsComplRestriction S W K) ≫ extendMap φ.τ₂ embeddingUpNat :=
  mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _
    (((embeddingUpNat.extendFunctor _).mapShortComplex.map φ).comm₂₃.symm)

/-- The second projection commutes with the map of section diagrams in each degree. -/
@[reassoc (attr := simp)]
lemma supportedSubmoduleSectionsMappingCoconeMap_f_snd_v
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L)
    (p q : ℤ) (hpq : p + -1 = q) :
    (supportedSubmoduleSectionsMappingCoconeMap S W K φ).f p ≫
        (mappingCocone.snd (moduleSectionsComplRestriction S' W' L)).v p q hpq =
      (mappingCocone.snd (moduleSectionsComplRestriction S W K)).v p q hpq ≫
        (extendMap φ.τ₃ embeddingUpNat).f q := by
  subst hpq
  exact mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _
    (((embeddingUpNat.extendFunctor _).mapShortComplex.map φ).comm₂₃.symm) p

/-- Maps of section diagrams act componentwise on relative cochains. -/
@[simp]
lemma relativeCoordinates_supportedSubmoduleSectionsMappingCoconeMap
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L)
    (p q : ℤ) (hpq : p + -1 = q) (a : (supportedSubmoduleSectionsMappingCocone S W K).X p) :
    mappingCocone.relativeCoordinates (moduleSectionsComplRestriction S' W' L) p q hpq
        ((supportedSubmoduleSectionsMappingCoconeMap S W K φ).f p a) =
      ((extendMap φ.τ₂ embeddingUpNat).f p
          (mappingCocone.relativeCoordinates (moduleSectionsComplRestriction S W K) p q hpq a).1,
        (extendMap φ.τ₃ embeddingUpNat).f q
          (mappingCocone.relativeCoordinates (moduleSectionsComplRestriction S W K) p q hpq a).2) :=
  mappingCocone.relativeCoordinates_map _ _ _ _
    (((embeddingUpNat.extendFunctor _).mapShortComplex.map φ).comm₂₃.symm) p q hpq a

/-- Identity diagrams induce the identity on the relative cone. -/
@[simp]
lemma supportedSubmoduleSectionsMappingCoconeMap_id :
    supportedSubmoduleSectionsMappingCoconeMap S W K
      (𝟙 (supportedSubmoduleSectionsShortComplex S W K)) = 𝟙 _ :=
  (sectionMappingCoconeFunctor (R := R)).map_id _

/-- Composition of diagrams induces composition of the relative cone maps. -/
@[simp]
lemma supportedSubmoduleSectionsMappingCoconeMap_comp {S'' : Closeds X} {W'' : Opens X}
    {M : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L)
    (ψ : supportedSubmoduleSectionsShortComplex S' W' L ⟶
      supportedSubmoduleSectionsShortComplex S'' W'' M) :
    supportedSubmoduleSectionsMappingCoconeMap S W K (φ ≫ ψ) =
      supportedSubmoduleSectionsMappingCoconeMap S W K φ ≫
        supportedSubmoduleSectionsMappingCoconeMap S' W' L ψ :=
  (sectionMappingCoconeFunctor (R := R)).map_comp φ ψ

/-- The supported-section-to-cocone comparison is natural in diagrams of section complexes. -/
@[reassoc]
lemma supportedSubmoduleSectionsToMappingCocone_naturality
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L) :
    extendMap φ.τ₁ embeddingUpNat ≫ supportedSubmoduleSectionsToMappingCocone S' W' L =
      supportedSubmoduleSectionsToMappingCocone S W K ≫
        supportedSubmoduleSectionsMappingCoconeMap S W K φ :=
  mappingCocone.liftShortComplex_naturality ((embeddingUpNat.extendFunctor _).mapShortComplex.map φ)

/-- The homology comparison is induced by the canonical supported-cochain inclusion,
after identifying the homology of extension by zero. -/
@[reassoc (attr := simp)]
lemma extendHomologyIso_hom_supportedSubmoduleSectionsMappingCoconeHomologyIso_hom (n : ℕ)
    [QuasiIsoAt (supportedSubmoduleSectionsToMappingCocone S W K) (n : ℤ)] :
    ((supportedSubmoduleSectionsShortComplex S W K).X₁.extendHomologyIso embeddingUpNat
      (embeddingUpNat_f n)).hom ≫
        (supportedSubmoduleSectionsMappingCoconeHomologyIso S W K n).hom =
      homologyMap (supportedSubmoduleSectionsToMappingCocone S W K) (n : ℤ) := by
  simp [supportedSubmoduleSectionsMappingCoconeHomologyIso]

/-- The mapping cocone homology computation respects diagrams of section complexes. -/
@[reassoc]
lemma supportedSubmoduleSectionsMappingCoconeHomologyIso_hom_naturality
    (φ : supportedSubmoduleSectionsShortComplex S W K ⟶
      supportedSubmoduleSectionsShortComplex S' W' L)
    (n : ℕ) [QuasiIsoAt (supportedSubmoduleSectionsToMappingCocone S W K) (n : ℤ)]
    [QuasiIsoAt (supportedSubmoduleSectionsToMappingCocone S' W' L) (n : ℤ)] :
    homologyMap φ.τ₁ n ≫ (supportedSubmoduleSectionsMappingCoconeHomologyIso S' W' L n).hom =
      (supportedSubmoduleSectionsMappingCoconeHomologyIso S W K n).hom ≫
        homologyMap (supportedSubmoduleSectionsMappingCoconeMap S W K φ) (n : ℤ) := by
  apply (cancel_epi ((supportedSubmoduleSectionsShortComplex S W K).X₁.extendHomologyIso
    embeddingUpNat (embeddingUpNat_f n)).hom).1
  rw [← Category.assoc, ← extendHomologyIso_hom_naturality φ.τ₁ embeddingUpNat (embeddingUpNat_f n),
    Category.assoc, extendHomologyIso_hom_supportedSubmoduleSectionsMappingCoconeHomologyIso_hom,
    extendHomologyIso_hom_supportedSubmoduleSectionsMappingCoconeHomologyIso_hom_assoc,
    ← homologyMap_comp, ← homologyMap_comp, supportedSubmoduleSectionsToMappingCocone_naturality]

variable {K} {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι]
  (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

/-- A flasque resolution computes right derived supported sections by the shifted cone
of ordinary section restriction. -/
def rightDerivedSupportedSubmoduleSectionsMappingCoconeIso (n : ℕ) :
    ((supportedSubmoduleSectionsFunctor (R := R) S W).rightDerived n).obj F ≅
      (supportedSubmoduleSectionsMappingCocone S W K).homology (n : ℤ) := by
  letI := quasiIso_supportedSubmoduleSectionsToMappingCocone S W K (fun m ↦ (hK m).epi _)
  exact rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque S ι hK W n ≪≫
    supportedSubmoduleSectionsMappingCoconeHomologyIso S W K n

/-- The right-derived comparison factors through the supported cohomology of the resolution. -/
lemma rightDerivedSupportedSubmoduleSectionsMappingCoconeIso_hom (n : ℕ) :
    letI := quasiIso_supportedSubmoduleSectionsToMappingCocone S W K (fun m ↦ (hK m).epi _)
    (rightDerivedSupportedSubmoduleSectionsMappingCoconeIso S W ι hK n).hom =
      (rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque S ι hK W n).hom ≫
        (supportedSubmoduleSectionsMappingCoconeHomologyIso S W K n).hom := (rfl)

/-- Supported Ext cohomology is the homology of the shifted restriction cone on any
flasque resolution of the coefficient sheaf. -/
def supportedModuleHMappingCoconeIso (n : ℕ) :
    ModuleCat.of R (F.supportedModuleH S W n) ≅
      (supportedSubmoduleSectionsMappingCocone S W K).homology (n : ℤ) :=
  ((rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).app F).symm ≪≫
    rightDerivedSupportedSubmoduleSectionsMappingCoconeIso S W ι hK n

/-- The supported Ext comparison agrees with the right-derived comparison. -/
@[simp]
lemma rightDerivedSupportedSubmoduleSectionsIso_hom_supportedModuleHMappingCoconeIso_hom (n : ℕ) :
    (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).hom.app F ≫
        (supportedModuleHMappingCoconeIso S W ι hK n).hom =
      (rightDerivedSupportedSubmoduleSectionsMappingCoconeIso S W ι hK n).hom :=
  Iso.hom_inv_id_assoc ((rightDerivedSupportedSubmoduleSectionsIso S W n).app F) _

end

end CategoryTheory.Sheaf
