/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
public import TauCeti.CategoryTheory.Abelian.AcyclicResolution
public import TauCeti.Topology.Sheaves.Flasque.Module
public import TauCeti.Topology.Sheaves.Flasque.Locality

/-!
# Flasque resolutions for supported sections

For a closed subset `S` of a topological space, the functor sending a sheaf of
modules `F` to its sheaf of sections supported in `S` is exact on short exact
sequences with flasque kernel. The same holds after taking sections on any open
`W`. Consequently flasque resolutions compute both right derived functors:
the sheaf-valued derived supported-section functor and the module-valued derived
functor of sections on `W` supported in `S`.

The comparisons are characterized through every augmentation-preserving map to
an injective resolution. Thus they do not depend on a chosen comparison map.
These results do not yet identify the derived sheaf functor with the
sheafification of the supported Ext presheaves.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* The Stacks Project, Cohomology of Sheaves, tag 09SY, and Derived Categories,
  tag 05T8.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace CochainComplex

universe u

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)

/-- Supported sections preserve a short exact sequence with flasque kernel. -/
theorem shortExact_map_supportedSubmoduleFunctor_of_isFlasque
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₁.obj] :
    (T.map (supportedSubmoduleFunctor S)).ShortExact := by
  let U := sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have : TopCat.Presheaf.IsFlasque (T.map U).X₁.obj :=
    TopCat.Presheaf.isFlasque_comp T.X₁.obj _
  have h := shortExact_map_supportedSectionsFunctor S
    (shortExact_map_sheafCompose_forget₂_moduleCat hT)
    (isZero_supportedHSheaf_succ_of_isFlasque (T.map U).X₁ S 0)
  have h' : ((T.map (supportedSubmoduleFunctor S)).map U).ShortExact := by
    rw [← ShortComplex.map_comp]
    apply (ShortComplex.shortExact_iff_of_iso
      (T.mapNatIso (supportedSubmoduleFunctorForgetIso (R := R) S))).2
    simpa only [ShortComplex.map_comp] using h
  exact ShortComplex.ShortExact.mk' (U.reflects_exact_of_faithful _ h'.exact)
    (U.mono_of_mono_map h'.mono_f) (U.epi_of_epi_map h'.epi_g)

/-- Taking sections supported in `S` on any open preserves short exact sequences
with flasque kernel. -/
theorem shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque (W : Opens X)
    {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))}
    (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₁.obj] :
    (T.map (supportedSubmoduleSectionsFunctor S W)).ShortExact := by
  let E := T.map (supportedSubmoduleFunctor S)
  have hE : E.ShortExact := shortExact_map_supportedSubmoduleFunctor_of_isFlasque S hT
  have : TopCat.Presheaf.IsFlasque E.X₁.obj :=
    isFlasque_supportedSubmoduleSheaf T.X₁ S
  have := hE.mono_f
  have : PreservesLimits ((sheafSections (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).obj (op W)) :=
    preservesLimits_of_natIso (sheafSectionsNatIsoEvaluation
      (J := Opens.grothendieckTopology X) (A := ModuleCat.{u} R) (X := W)).symm
  dsimp only [supportedSubmoduleSectionsFunctor]
  rw [ShortComplex.map_comp]
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact hE.exact.map_of_mono_of_preservesKernel _ hE.mono_f inferInstance
  · exact Functor.map_mono ((sheafSections (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)).obj (op W)) E.f
  · exact (ModuleCat.epi_iff_surjective _).2 (hE.surjective_app_of_isFlasque (op W))

private lemma flasque_cokernel
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hT : T.ShortExact) (h₁ : isFlasque X _ T.X₁) (h₂ : isFlasque X _ T.X₂) :
    isFlasque X _ T.X₃ :=
  have : TopCat.Presheaf.IsFlasque T.X₁.obj := isFlasque_iff.mp h₁
  have : TopCat.Presheaf.IsFlasque T.X₂.obj := isFlasque_iff.mp h₂
  isFlasque_iff.mpr hT.isFlasque_X₃_of_isFlasque

private lemma supported_exact_on_flasque
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hT : T.ShortExact) (h₁ : isFlasque X _ T.X₁) (_ : isFlasque X _ T.X₂) :
    (T.map (supportedSubmoduleFunctor S)).ShortExact :=
  have : TopCat.Presheaf.IsFlasque T.X₁.obj := isFlasque_iff.mp h₁
  shortExact_map_supportedSubmoduleFunctor_of_isFlasque S hT

private lemma supported_sections_exact_on_flasque (W : Opens X)
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)))
    (hT : T.ShortExact) (h₁ : isFlasque X _ T.X₁) (_ : isFlasque X _ T.X₂) :
    (T.map (supportedSubmoduleSectionsFunctor S W)).ShortExact :=
  have : TopCat.Presheaf.IsFlasque T.X₁.obj := isFlasque_iff.mp h₁
  shortExact_map_supportedSubmoduleSectionsFunctor_of_isFlasque S W hT

variable {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
  {K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) ℕ}
  (ι : (single₀ _).obj F ⟶ K) [QuasiIso ι]
  (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj)

include hK in
/-- Applying sheaf-valued supported sections to a comparison from a flasque
resolution to an injective resolution gives a quasi-isomorphism. -/
theorem quasiIso_map_supportedSubmoduleFunctor_of_isFlasque
    (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    QuasiIso (((supportedSubmoduleFunctor S).mapHomologicalComplex _).map φ) :=
  InjectiveResolution.quasiIso_map_of_comp_eq _ (isFlasque X _)
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) flasque_cokernel
    (supported_exact_on_flasque S) ι (fun n ↦ isFlasque_iff.mpr (hK n)) I φ hφ

/-- A flasque resolution computes the sheaf-valued right derived supported sections. -/
noncomputable def rightDerivedSupportedSubmoduleObjIsoOfIsFlasque (n : ℕ) :
    ((supportedSubmoduleFunctor S).rightDerived n).obj F ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((supportedSubmoduleFunctor S).mapHomologicalComplex _).obj K) :=
  Functor.rightDerivedObjIsoOfResolution _ (isFlasque X _)
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) flasque_cokernel
    (supported_exact_on_flasque S) ι (fun n ↦ isFlasque_iff.mpr (hK n)) n

/-- Characterization of the flasque supported-section comparison through any
augmentation-preserving map to any injective resolution. -/
@[reassoc]
lemma rightDerivedSupportedSubmoduleObjIsoOfIsFlasque_hom_comp_homologyMap
    (n : ℕ) (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    (rightDerivedSupportedSubmoduleObjIsoOfIsFlasque S ι hK n).hom ≫
      ((supportedSubmoduleFunctor S).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ =
      (I.isoRightDerivedObj (supportedSubmoduleFunctor S) n).hom :=
  Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap _ _ _ _ _ ι
    (fun n ↦ isFlasque_iff.mpr (hK n)) n I φ hφ

include hK in
/-- Applying sections on `W` supported in `S` to a comparison from a flasque
resolution to an injective resolution gives a quasi-isomorphism. -/
theorem quasiIso_map_supportedSubmoduleSectionsFunctor_of_isFlasque (W : Opens X)
    (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex) (hφ : ι ≫ φ = I.ι) :
    QuasiIso (((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex _).map φ) :=
  InjectiveResolution.quasiIso_map_of_comp_eq _ (isFlasque X _)
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) flasque_cokernel
    (supported_sections_exact_on_flasque S W) ι (fun n ↦ isFlasque_iff.mpr (hK n)) I φ hφ

/-- A flasque resolution computes the module-valued right derived functor of
sections on `W` supported in `S`. -/
noncomputable def rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque
    (W : Opens X) (n : ℕ) :
    ((supportedSubmoduleSectionsFunctor S W).rightDerived n).obj F ≅
      (HomologicalComplex.homologyFunctor _ _ n).obj
        (((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex _).obj K) :=
  Functor.rightDerivedObjIsoOfResolution _ (isFlasque X _)
    (fun _ _ ↦ isFlasque_iff.mpr (isFlasque_of_injective_moduleCat _)) flasque_cokernel
    (supported_sections_exact_on_flasque S W) ι (fun n ↦ isFlasque_iff.mpr (hK n)) n

/-- Characterization of the module-valued flasque comparison through any
augmentation-preserving map to any injective resolution. -/
@[reassoc]
lemma rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque_hom_comp_homologyMap
    (W : Opens X) (n : ℕ) (I : InjectiveResolution F) (φ : K ⟶ I.cocomplex)
    (hφ : ι ≫ φ = I.ι) :
    (rightDerivedSupportedSubmoduleSectionsObjIsoOfIsFlasque S ι hK W n).hom ≫
      ((supportedSubmoduleSectionsFunctor S W).mapHomologicalComplex _ ⋙
        HomologicalComplex.homologyFunctor _ _ n).map φ =
      (I.isoRightDerivedObj (supportedSubmoduleSectionsFunctor S W) n).hom :=
  Functor.rightDerivedObjIsoOfResolution_hom_comp_homologyMap _ _ _ _ _ ι
    (fun n ↦ isFlasque_iff.mpr (hK n)) n I φ hφ

end CategoryTheory.Sheaf
