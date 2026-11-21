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
`W` embed in the relative complex of restriction from `W` to `W ∖ S`. If the terms
of `K` are flasque, this embedding is a quasi-isomorphism: restriction is degreewise
surjective and its kernel is precisely the supported sections.

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

variable (K : CochainComplex
  (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ)

/-- Supported sections, sections, and restriction to the complement, as a short complex
of nonnegative complexes. It is short exact when the terms of `K` are flasque. -/
abbrev supportedSectionsShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (((supportedSubmoduleSectionsι S W).mapHomologicalComplex _).app K)
    ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (S.complInclusion W).op).mapHomologicalComplex _).app K)
    (by
      ext n s
      -- Normalize evaluation of the mapped natural transformations and composition.
      change (K.X n).obj.map (S.complInclusion W).op
        ((supportedSubmoduleSectionsι S W).app (K.X n) s) = 0
      erw [supportedSubmoduleSectionsι_app_apply]
      exact ((K.X n).mem_supportedSubmodule_iff).1 s.property)

/-- Flasqueness makes the sequence of supported sections and restriction short exact,
without requiring an exactness assumption on `K` itself. -/
lemma shortExact_supportedSectionsShortComplex
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj) :
    (supportedSectionsShortComplex S W K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hK n
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · -- Expose only the evaluation wrappers, not the supported-section submodule.
    change Function.Exact ((supportedSubmoduleSectionsι S W).app (K.X n))
      ((K.X n).obj.map (S.complInclusion W).op)
    intro s
    constructor
    · intro hs
      exact ⟨⟨s, ((K.X n).mem_supportedSubmodule_iff).2 hs⟩,
        supportedSubmoduleSectionsι_app_apply S W (K.X n) _⟩
    · rintro ⟨t, rfl⟩
      erw [supportedSubmoduleSectionsι_app_apply]
      exact ((K.X n).mem_supportedSubmodule_iff).1 t.property
  · -- The first component is evaluation of the inclusion natural transformation.
    change Function.Injective ((supportedSubmoduleSectionsι S W).app (K.X n))
    intro s t h
    apply Subtype.ext
    erw [supportedSubmoduleSectionsι_app_apply, supportedSubmoduleSectionsι_app_apply] at h
    exact h
  · exact (ModuleCat.epi_iff_surjective ((K.X n).obj.map (S.complInclusion W).op)).1
      inferInstance

/-- A map of coefficient complexes gives the corresponding diagram of section complexes. -/
def supportedSectionsShortComplexMap
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (f : K ⟶ L) : supportedSectionsShortComplex S W K ⟶
      supportedSectionsShortComplex S W L where
  τ₁ := ((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex _).map f
  τ₂ := (((sheafSections _ (ModuleCat.{u} R)).obj (op W)).mapHomologicalComplex _).map f
  τ₃ := (((sheafSections _ (ModuleCat.{u} R)).obj (op (W ⊓ S.compl))).mapHomologicalComplex
    _).map f
  comm₁₂ := ((supportedSubmoduleSectionsι S W).mapHomologicalComplex _).naturality f
  comm₂₃ := (((sheafSections _ (ModuleCat.{u} R)).map
    (S.complInclusion W).op).mapHomologicalComplex _).naturality f

@[simp]
lemma supportedSectionsShortComplexMap_τ₁
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (f : K ⟶ L) : (supportedSectionsShortComplexMap S W K f).τ₁ =
      ((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex _).map f := (rfl)

@[simp]
lemma supportedSectionsShortComplexMap_τ₂
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (f : K ⟶ L) : (supportedSectionsShortComplexMap S W K f).τ₂ =
      (((sheafSections _ (ModuleCat.{u} R)).obj (op W)).mapHomologicalComplex _).map f := (rfl)

@[simp]
lemma supportedSectionsShortComplexMap_τ₃
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (f : K ⟶ L) : (supportedSectionsShortComplexMap S W K f).τ₃ =
      (((sheafSections _ (ModuleCat.{u} R)).obj (op (W ⊓ S.compl))).mapHomologicalComplex
        _).map f := (rfl)

/-- Shrinking the open domain gives a diagram of section short complexes. -/
def supportedSectionsShortComplexRestrict {W' : Opens X} (i : W' ⟶ W) :
    supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' K where
  τ₁ := ((supportedSubmoduleSectionsRestrict S i).mapHomologicalComplex _).app K
  τ₂ := (((sheafSections _ (ModuleCat.{u} R)).map i.op).mapHomologicalComplex _).app K
  τ₃ := (((sheafSections _ (ModuleCat.{u} R)).map
    (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op).mapHomologicalComplex _).app K
  comm₁₂ := by
    ext n s
    -- Evaluate the mapped natural transformations before using their section formulas.
    change (supportedSubmoduleSectionsι S W').app (K.X n)
        ((supportedSubmoduleSectionsRestrict S i).app (K.X n) s) =
      (K.X n).obj.map i.op ((supportedSubmoduleSectionsι S W).app (K.X n) s)
    erw [supportedSubmoduleSectionsι_app_apply,
      coe_supportedSubmoduleSectionsRestrict_app_apply, supportedSubmoduleSectionsι_app_apply]
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro n
    have h : i.op ≫ (S.complInclusion W').op = (S.complInclusion W).op ≫
        (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op := Subsingleton.elim _ _
    -- Evaluation of both mapped natural transformations is ordinary section restriction.
    change (K.X n).obj.map i.op ≫ (K.X n).obj.map (S.complInclusion W').op =
      (K.X n).obj.map (S.complInclusion W).op ≫
        (K.X n).obj.map (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op
    simpa only [Functor.map_comp] using congrArg (fun j ↦ (K.X n).obj.map j) h

@[simp]
lemma supportedSectionsShortComplexRestrict_τ₁ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSectionsShortComplexRestrict S W K i).τ₁ =
      ((supportedSubmoduleSectionsRestrict S i).mapHomologicalComplex _).app K := (rfl)

@[simp]
lemma supportedSectionsShortComplexRestrict_τ₂ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSectionsShortComplexRestrict S W K i).τ₂ =
      (((sheafSections _ (ModuleCat.{u} R)).map i.op).mapHomologicalComplex _).app K := (rfl)

@[simp]
lemma supportedSectionsShortComplexRestrict_τ₃ {W' : Opens X} (i : W' ⟶ W) :
    (supportedSectionsShortComplexRestrict S W K i).τ₃ =
      (((sheafSections _ (ModuleCat.{u} R)).map
        (homOfLE (inf_le_inf_right S.compl (leOfHom i))).op).mapHomologicalComplex _).app K :=
  (rfl)

noncomputable section

/-- Restriction of the section complexes, extended by zero to integer degrees. -/
abbrev supportedSectionsRestriction :=
  extendMap (supportedSectionsShortComplex S W K).g ComplexShape.embeddingUpNat

/-- The cone of restriction, shifted by `-1`, on a nonnegative complex of sheaves. -/
abbrev supportedSectionsCone : CochainComplex (ModuleCat.{u} R) ℤ :=
  mappingCocone (supportedSectionsRestriction S W K)

/-- The canonical inclusion of supported cochains in the shifted restriction cone.
Its relative second coordinate is zero; no choice of extension is involved. -/
def supportedSectionsToCone :
    (HomologicalComplex.extend
      (((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K)
        ComplexShape.embeddingUpNat) ⟶ supportedSectionsCone S W K :=
  mappingCocone.lift (supportedSectionsRestriction S W K)
    (extendMap (supportedSectionsShortComplex S W K).f ComplexShape.embeddingUpNat) 0
    (by
      rw [HomComplex.δ_zero, zero_add, ← extendMap_comp]
      rw [(supportedSectionsShortComplex S W K).zero, extendMap_zero,
        HomComplex.Cochain.ofHom_zero])

/-- The first projection of the supported-cochain inclusion is the usual inclusion
into all cochains on `W`. -/
@[reassoc (attr := simp)]
lemma supportedSectionsToCone_fst :
    supportedSectionsToCone S W K ≫ mappingCocone.fst (supportedSectionsRestriction S W K) =
      extendMap (supportedSectionsShortComplex S W K).f ComplexShape.embeddingUpNat :=
  mappingCocone.lift_fst _ _ _ _

/-- In relative coordinates a supported cochain goes to `(a,0)`. -/
@[simp]
lemma relativeCoordinates_supportedSectionsToCone (p q : ℤ) (hpq : p + -1 = q)
    (a : (((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K
      |>.extend ComplexShape.embeddingUpNat).X p) :
    mappingCocone.relativeCoordinates (supportedSectionsRestriction S W K) p q hpq
        ((supportedSectionsToCone S W K).f p a) =
      ((extendMap (supportedSectionsShortComplex S W K).f ComplexShape.embeddingUpNat).f p a,
        0) := by
  rw [mappingCocone.relativeCoordinates_apply]
  apply Prod.ext
  · exact congrArg (fun f ↦ f a)
      (HomologicalComplex.congr_hom (supportedSectionsToCone_fst S W K) p)
  · simp [supportedSectionsToCone, ← ModuleCat.comp_apply,
      mappingCocone.lift_f_snd_v]

/-- Supported cochains and the shifted restriction cone are quasi-isomorphic for every
complex of flasque sheaves. -/
theorem quasiIso_supportedSectionsToCone
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj) :
    QuasiIso (supportedSectionsToCone S W K) :=
  mappingCocone.quasiIso_lift_of_shortExact
    (S := (supportedSectionsShortComplex S W K).map
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)))
    ((shortExact_supportedSectionsShortComplex S W K hK).extend ComplexShape.embeddingUpNat)

/-- The cone computes the homology of supported cochains in every nonnegative degree. -/
def supportedSectionsConeHomologyIso
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj) (n : ℕ) :
    (((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K).homology n ≅
      (supportedSectionsCone S W K).homology (n : ℤ) := by
  letI := quasiIso_supportedSectionsToCone S W K hK
  exact (((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K
    |>.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm ≪≫
      isoOfQuasiIsoAt (supportedSectionsToCone S W K) (n : ℤ)

/-- A commutative diagram of section short complexes induces a map of relative cones.
This applies equally to restriction of opens and to maps of coefficient complexes. -/
def supportedSectionsConeMap {W' : Opens X}
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' L) :
    supportedSectionsCone S W K ⟶ supportedSectionsCone S W' L :=
  (mappingCone.map _ _ (extendMap φ.τ₂ ComplexShape.embeddingUpNat)
    (extendMap φ.τ₃ ComplexShape.embeddingUpNat)
    (by rw [← extendMap_comp, ← extendMap_comp, φ.comm₂₃]))⟦(-1 : ℤ)⟧'

/-- Maps of section diagrams act componentwise on relative cochains. -/
@[simp]
lemma relativeCoordinates_supportedSectionsConeMap {W' : Opens X}
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' L)
    (p q : ℤ) (hpq : p + -1 = q) (a : (supportedSectionsCone S W K).X p) :
    mappingCocone.relativeCoordinates (supportedSectionsRestriction S W' L) p q hpq
        ((supportedSectionsConeMap S W K φ).f p a) =
      ((extendMap φ.τ₂ ComplexShape.embeddingUpNat).f p
          (mappingCocone.relativeCoordinates (supportedSectionsRestriction S W K) p q hpq a).1,
        (extendMap φ.τ₃ ComplexShape.embeddingUpNat).f q
          (mappingCocone.relativeCoordinates (supportedSectionsRestriction S W K) p q hpq a).2) :=
  mappingCocone.relativeCoordinates_map _ _ _ _ _ p q hpq a

/-- Identity diagrams induce the identity on the relative cone. -/
@[simp]
lemma supportedSectionsConeMap_id :
    supportedSectionsConeMap S W K (𝟙 (supportedSectionsShortComplex S W K)) = 𝟙 _ := by
  simp [supportedSectionsConeMap, supportedSectionsCone, mappingCocone, mappingCone.map_id]

/-- Composition of diagrams induces composition of the relative cone maps. -/
@[simp]
lemma supportedSectionsConeMap_comp {W' W'' : Opens X}
    {L M : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' L)
    (ψ : supportedSectionsShortComplex S W' L ⟶ supportedSectionsShortComplex S W'' M) :
    supportedSectionsConeMap S W K (φ ≫ ψ) =
      supportedSectionsConeMap S W K φ ≫ supportedSectionsConeMap S W' L ψ := by
  dsimp only [supportedSectionsConeMap]
  simp only [ShortComplex.comp_τ₂, ShortComplex.comp_τ₃, extendMap_comp]
  erw [mappingCone.map_comp]
  exact Functor.map_comp _ _ _

/-- The supported-section-to-cone comparison is natural in diagrams of section complexes. -/
@[reassoc]
lemma supportedSectionsToCone_naturality {W' : Opens X}
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' L) :
    extendMap φ.τ₁ ComplexShape.embeddingUpNat ≫ supportedSectionsToCone S W' L =
      supportedSectionsToCone S W K ≫ supportedSectionsConeMap S W K φ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCocone.ext_to _ p (p + -1) rfl
  · have hmap : supportedSectionsConeMap S W K φ ≫
        mappingCocone.fst (supportedSectionsRestriction S W' L) =
        mappingCocone.fst (supportedSectionsRestriction S W K) ≫
          extendMap φ.τ₂ ComplexShape.embeddingUpNat :=
      mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst _ _ _ _ _
    have h : (extendMap φ.τ₁ ComplexShape.embeddingUpNat ≫
          supportedSectionsToCone S W' L) ≫
          mappingCocone.fst (supportedSectionsRestriction S W' L) =
        (supportedSectionsToCone S W K ≫ supportedSectionsConeMap S W K φ) ≫
          mappingCocone.fst (supportedSectionsRestriction S W' L) := by
      rw [Category.assoc, supportedSectionsToCone_fst, Category.assoc, hmap,
        ← Category.assoc, supportedSectionsToCone_fst, ← extendMap_comp,
        ← extendMap_comp, φ.comm₁₂]
    exact HomologicalComplex.congr_hom h p
  · have hmap : (supportedSectionsConeMap S W K φ).f p ≫
        (mappingCocone.snd (supportedSectionsRestriction S W' L)).v p (p + -1) rfl =
        (mappingCocone.snd (supportedSectionsRestriction S W K)).v p (p + -1) rfl ≫
          (extendMap φ.τ₃ ComplexShape.embeddingUpNat).f (p + -1) :=
      mappingCocone.shiftFunctor_map_mappingCone_map_f_snd_v _ _ _ _ _ p
    simp only [HomologicalComplex.comp_f, Category.assoc, hmap]
    simp [supportedSectionsToCone, ← Category.assoc, mappingCocone.lift_f_snd_v]

/-- The homology comparison is induced by the canonical supported-cochain inclusion,
after identifying the homology of extension by zero. -/
@[reassoc (attr := simp)]
lemma extendHomologyIso_hom_supportedSectionsConeHomologyIso_hom
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj) (n : ℕ) :
    ((((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K
      |>.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)).hom ≫
        (supportedSectionsConeHomologyIso S W K hK n).hom =
      homologyMap (supportedSectionsToCone S W K) (n : ℤ) := by
  have := quasiIso_supportedSectionsToCone S W K hK
  dsimp only [supportedSectionsConeHomologyIso, Iso.trans_hom, Iso.symm_hom]
  erw [Iso.hom_inv_id_assoc]
  exact isoOfQuasiIsoAt_hom _ _

/-- The cone homology computation respects restriction and coefficient diagrams. -/
@[reassoc]
lemma supportedSectionsConeHomologyIso_hom_naturality {W' : Opens X}
    {L : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
    (φ : supportedSectionsShortComplex S W K ⟶ supportedSectionsShortComplex S W' L)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)
    (hL : ∀ n, TopCat.Presheaf.IsFlasque (L.X n).obj) (n : ℕ) :
    homologyMap φ.τ₁ n ≫ (supportedSectionsConeHomologyIso S W' L hL n).hom =
      (supportedSectionsConeHomologyIso S W K hK n).hom ≫
        homologyMap (supportedSectionsConeMap S W K φ) (n : ℤ) := by
  apply (cancel_epi
    ((((supportedSubmoduleSectionsFunctor (R := R) S W).mapHomologicalComplex _).obj K
      |>.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)).hom).1
  rw [← Category.assoc, ← extendHomologyIso_hom_naturality φ.τ₁
    ComplexShape.embeddingUpNat (j := n) rfl, Category.assoc,
    extendHomologyIso_hom_supportedSectionsConeHomologyIso_hom,
    extendHomologyIso_hom_supportedSectionsConeHomologyIso_hom_assoc]
  erw [← homologyMap_comp, ← homologyMap_comp]
  exact congrArg (fun f ↦ homologyMap f (n : ℤ))
    (supportedSectionsToCone_naturality S W K φ)

variable {K} {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι]
  (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

/-- A flasque resolution computes right derived supported sections by the shifted cone
of ordinary section restriction. -/
def rightDerivedSupportedSectionsConeIso (n : ℕ) :
    ((supportedSubmoduleSectionsFunctor (R := R) S W).rightDerived n).obj F ≅
      (supportedSectionsCone S W K).homology (n : ℤ) :=
  rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque S ι hK W n ≪≫
    supportedSectionsConeHomologyIso S W K hK n

/-- Supported Ext cohomology is the homology of the shifted restriction cone on any
flasque resolution of the coefficient sheaf. -/
def supportedModuleHConeIso (n : ℕ) :
    ModuleCat.of R (F.supportedModuleH S W n) ≅
      (supportedSectionsCone S W K).homology (n : ℤ) :=
  ((rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).app F).symm ≪≫
    rightDerivedSupportedSectionsConeIso S W ι hK n

end

end CategoryTheory.Sheaf
