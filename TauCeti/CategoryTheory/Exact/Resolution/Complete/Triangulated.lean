/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Horseshoe
public import TauCeti.CategoryTheory.Exact.Resolution.Complete.Stable
public import TauCeti.CategoryTheory.Exact.Stable.Pretriangulated

/-!
# The stable category and `K_ac(P)` as triangulated categories

Let `E` be a Frobenius exact structure on `C`. The complete-resolution functor from the stable
category to the homotopy category `K(C)` is a triangle functor, for Happel's triangulation of the
stable category. Consequently `K_ac(P)`, the complexes homotopy equivalent to spliced complexes
of complete resolutions, is a triangulated subcategory of `K(C)`, and the equivalence between
the stable category and `K_ac(P)` is a triangle equivalence.

The functor commutes with shifts: the shift by one of a complete resolution of `X` is a complete
resolution of the cokernel of `X ↪ X⁰`, which represents the suspension of `X`. It sends the
standard triangle of a conflation `X ↪ Y ↠ Z` to the triangle of the degreewise split sequence of
complete resolutions given by the horseshoe lemma, which is distinguished in `K(C)`. The two
connecting maps are compared on cycles in degree zero, where two maps of complete resolutions
agree in `K(C)` exactly when they agree in the stable category.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.stableToHomotopyCategoryCommShift`: the functor from the
  stable category to `K(C)` commutes with the shifts.
* `TauCeti.ExactStructure.IsFrobenius.stableToHomotopyCategory_isTriangulated`: it is a triangle
  functor.
* `TauCeti.ExactStructure.IsFrobenius.completeResolutionComplex_isTriangulated`: `K_ac(P)` is a
  triangulated subcategory of `K(C)`.
* `TauCeti.ExactStructure.IsFrobenius.stableToCompleteResolutionHomotopyCategory_isTriangulated`:
  the equivalence between the stable category and `K_ac(P)` is a triangle functor.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379--417.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

namespace CompleteResolution

variable (r : E.CompleteResolution)

/-- The complete resolution shifted by one: its conflations are `Zⁿ⁺¹ ↪ Xⁿ⁺¹ ↠ Zⁿ⁺²`, with the
inflations negated so that its spliced complex is the shift of the spliced complex of `r`. -/
abbrev shift : E.CompleteResolution where
  Z n := r.Z (n + 1)
  X n := r.X (n + 1)
  ι n := -r.ι (n + 1)
  π n := r.π (n + 1)
  ι_π n := by simp
  conflation n := E.conflation_of_iso (S := r.shortComplex (n + 1))
    (ShortComplex.isoMk { hom := -𝟙 _, inv := -𝟙 _ } (Iso.refl _) (Iso.refl _) (by simp)
      (by simp)) (r.conflation (n + 1))
  projectiveInjective n := r.projectiveInjective (n + 1)

/-- The spliced complex of the shifted complete resolution is the shift of the spliced complex. -/
noncomputable def shiftComplexIso : r.shift.complex ≅ r.complex⟦(1 : ℤ)⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    rintro i j rfl
    rw [CochainComplex.shiftFunctor_obj_d', complex_d, complex_d]
    simp [d_def])

@[simp]
theorem shiftComplexIso_hom_f (n : ℤ) : (r.shiftComplexIso.hom).f n = 𝟙 _ := by
  simp only [shiftComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.refl_hom]

@[simp]
theorem shiftComplexIso_inv_f (n : ℤ) : (r.shiftComplexIso.inv).f n = 𝟙 _ := by
  simp only [shiftComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f, Iso.refl_inv]
  rfl

variable {r} {r' : E.CompleteResolution}

/-- The map of shifted complete resolutions induced by a map of complete resolutions. -/
noncomputable def shiftMap (φ : r.complex ⟶ r'.complex) : r.shift.complex ⟶ r'.shift.complex :=
  r.shiftComplexIso.hom ≫ φ⟦(1 : ℤ)⟧' ≫ r'.shiftComplexIso.inv

@[simp]
theorem shiftMap_f (φ : r.complex ⟶ r'.complex) (n : ℤ) : (shiftMap φ).f n = φ.f (n + 1) := by
  simp only [shiftMap, HomologicalComplex.comp_f, shiftComplexIso_hom_f, shiftComplexIso_inv_f,
    CochainComplex.shiftFunctor_map_f']
  exact (Category.id_comp _).trans (Category.comp_id _)

@[reassoc]
theorem shiftMap_comp_shiftComplexIso_hom (φ : r.complex ⟶ r'.complex) :
    shiftMap φ ≫ r'.shiftComplexIso.hom = r.shiftComplexIso.hom ≫ φ⟦(1 : ℤ)⟧' := by
  simp [shiftMap]

/-- The morphism induced on the cycles in degree zero by the shift of a map is the morphism it
induces on the cokernels of `Z⁰ ↪ X⁰`. -/
@[reassoc]
theorem π_cyclesMap_shiftMap (φ : r.complex ⟶ r'.complex) :
    r.π 0 ≫ cyclesMap (shiftMap φ) = φ.f 0 ≫ r'.π 0 := by
  rw [← cancel_mono (r'.shift.ι 0), Category.assoc, cyclesMap_ι, shiftMap_f]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_inj]
  rw [← Category.assoc, ← r.d_def, ← f_comp_d, r'.d_def, Category.assoc]

/-- Two maps of complete resolutions agree in the homotopy category exactly when the difference
of the morphisms they induce on the cycles in degree zero factors through a projective-injective
object. -/
theorem quotient_map_eq_iff (φ ψ : r.complex ⟶ r'.complex) :
    (HomotopyCategory.quotient C _).map φ = (HomotopyCategory.quotient C _).map ψ ↔
      E.projectiveInjective.FactorsThrough (cyclesMap φ - cyclesMap ψ) := by
  rw [← nonempty_homotopy_zero_iff (φ := φ - ψ) (by simp [Preadditive.comp_sub,
    Preadditive.sub_comp])]
  exact ⟨fun h ↦ ⟨Homotopy.equivSubZero (HomotopyCategory.homotopyOfEq _ _ h)⟩,
    fun ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _ (Homotopy.equivSubZero.symm h)⟩

end CompleteResolution

namespace IsFrobenius

variable (hE : E.IsFrobenius)

/-- On the image of an object of `C`, the functor from the stable category to the homotopy
category is the complete-resolution functor. -/
@[simp]
theorem stableToHomotopyCategory_obj_projectiveStableFunctor_obj (X : C) :
    hE.stableToHomotopyCategory.obj (E.projectiveStableFunctor.obj X) =
      hE.completeResolutionFunctor.obj X :=
  rfl

/-- On the image of a morphism of `C`, the functor from the stable category to the homotopy
category is the complete-resolution functor. -/
@[simp]
theorem stableToHomotopyCategory_map_projectiveStableFunctor_map {X Y : C} (f : X ⟶ Y) :
    hE.stableToHomotopyCategory.map (E.projectiveStableFunctor.map f) =
      hE.completeResolutionFunctor.map f :=
  rfl

include hE in
/-- Two maps of complete resolutions agree in the homotopy category exactly when the morphisms
they induce on the cycles in degree zero agree in the stable category. -/
theorem quotient_map_eq_iff {r r' : E.CompleteResolution} (φ ψ : r.complex ⟶ r'.complex) :
    (HomotopyCategory.quotient C _).map φ = (HomotopyCategory.quotient C _).map ψ ↔
      E.projectiveStableFunctor.map (CompleteResolution.cyclesMap φ) =
        E.projectiveStableFunctor.map (CompleteResolution.cyclesMap ψ) := by
  rw [CompleteResolution.quotient_map_eq_iff, ← sub_eq_zero, ← Functor.map_sub,
    ExactStructure.projectiveStableFunctor_map_eq_zero_iff, hE.projectiveInjective_eq_isProjective]

/-- The first conflation `X ↪ X⁰ ↠ Z¹` of the chosen complete resolution of `X`, as a relative
injective presentation of `X`. -/
noncomputable abbrev completeResolutionPresentation (X : C) : E.InjectivePresentation X where
  I := (hE.completeResolution X).X 0
  K := (hE.completeResolution X).Z (0 + 1)
  i := (hE.completeResolutionIso X).inv ≫ (hE.completeResolution X).ι 0
  p := (hE.completeResolution X).π 0
  zero := by simp
  conflation := E.conflation_of_iso (S := (hE.completeResolution X).shortComplex 0)
    (ShortComplex.isoMk (hE.completeResolutionIso X) (Iso.refl _) (Iso.refl _) (by simp)
      (by simp)) ((hE.completeResolution X).conflation 0)
  isInjective := (hE.completeResolution X).isInjective_X 0

/-- Suspension computed from the complete resolutions: `X` goes to the cycles `Z¹` of its chosen
complete resolution. -/
noncomputable abbrev completeResolutionSuspension : C ⥤ E.ProjectiveStableCategory :=
  E.suspensionToStableOfPresentations hE.completeResolutionPresentation
    fun _ ↦ hE.isProjective_I _

/-- Stable suspension is naturally the suspension computed from complete resolutions. -/
noncomputable def stableSuspensionIsoCompleteResolutionSuspension :
    E.projectiveStableFunctor ⋙ hE.stableSuspension ≅ hE.completeResolutionSuspension :=
  NatIso.ofComponents (fun X ↦ eqToIso (hE.stableSuspension_obj_projectiveStableFunctor_obj X) ≪≫
      (hE.projectiveStableIsoSuspensionObj (hE.completeResolutionPresentation X)).symm ≪≫
      eqToIso (E.suspensionToStableOfPresentations_obj _ _ X).symm)
    (fun {X Y} f ↦ by
      -- Both sides are induced by `f` from the chosen presentation of `X` to the complete
      -- resolution presentation of `Y`.
      have h₁ := E.projectiveStableFunctor_map_cokernelMap_comp (hE.suspensionPresentation X)
        (hE.suspensionPresentation Y) (hE.completeResolutionPresentation Y)
        (hE.isProjective_I _) f (𝟙 Y)
      have h₂ := E.projectiveStableFunctor_map_cokernelMap_comp (hE.suspensionPresentation X)
        (hE.completeResolutionPresentation X) (hE.completeResolutionPresentation Y)
        (hE.isProjective_I _) (𝟙 X) f
      rw [Category.comp_id] at h₁
      rw [Category.id_comp] at h₂
      simp [stableSuspension_map_projectiveStableFunctor_map,
        suspensionToStableOfPresentations_map, ← reassoc_of% h₁, ← reassoc_of% h₂])

/-- The complete resolution of the cycles `Z¹` of the complete resolution of `X` is homotopy
equivalent to the shifted complete resolution of `X`. -/
noncomputable abbrev shiftHomotopyEquiv (X : C) :
    HomotopyEquiv (hE.completeResolution ((hE.completeResolution X).Z (0 + 1))).complex
      (hE.completeResolution X).shift.complex :=
  CompleteResolution.homotopyEquiv _ _ (hE.completeResolutionIso _)

/-- The suspension comparison on maps: the lift of the morphism induced by `f` on cycles `Z¹`
agrees, in the homotopy category, with the shift of the lift of `f`. -/
@[reassoc]
theorem quotient_map_liftMap_cokernelMap {X Y : C} (f : X ⟶ Y) :
    (HomotopyCategory.quotient C _).map
        (hE.liftMap ((hE.completeResolutionPresentation X).cokernelMap
          (hE.completeResolutionPresentation Y) f)) ≫
      (HomotopyCategory.quotient C _).map (hE.shiftHomotopyEquiv Y).hom =
    (HomotopyCategory.quotient C _).map (hE.shiftHomotopyEquiv X).hom ≫
      (HomotopyCategory.quotient C _).map (CompleteResolution.shiftMap (hE.liftMap f)) := by
  rw [← Functor.map_comp, ← Functor.map_comp, hE.quotient_map_eq_iff]
  simp only [CompleteResolution.cyclesMap_comp, cyclesMap_liftMap,
    CompleteResolution.cyclesMap_homotopyEquiv_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Functor.map_comp]
  congr 1
  exact E.projectiveStableFunctor_map_cokernelMap_eq _ _ (hE.isProjective_I _) f
    ((hE.liftMap f).f 0) _ (by simp) (CompleteResolution.π_cyclesMap_shiftMap _)

/-- The complete-resolution functor intertwines suspension, computed from complete
resolutions, with the shift by one of the homotopy category. -/
noncomputable def completeResolutionSuspensionCompIso :
    hE.completeResolutionSuspension ⋙ hE.stableToHomotopyCategory ≅
      hE.completeResolutionFunctor ⋙
        shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) :=
  NatIso.ofComponents (fun X ↦
    hE.stableToHomotopyCategory.mapIso (eqToIso (E.suspensionToStableOfPresentations_obj _ _ X)) ≪≫
      eqToIso (hE.completeResolutionFunctor_obj _) ≪≫
      HomotopyCategory.isoOfHomotopyEquiv (hE.shiftHomotopyEquiv X) ≪≫
      (HomotopyCategory.quotient C _).mapIso (hE.completeResolution X).shiftComplexIso ≪≫
      ((HomotopyCategory.quotient C _).commShiftIso (1 : ℤ)).app _ ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso (eqToIso (hE.completeResolutionFunctor_obj X).symm))
    (fun {X Y} f ↦ by
      have hc : hE.stableToHomotopyCategory.map (E.projectiveStableFunctor.map
          ((hE.completeResolutionPresentation X).cokernelMap
            (hE.completeResolutionPresentation Y) f)) =
          hE.completeResolutionFunctor.map ((hE.completeResolutionPresentation X).cokernelMap
            (hE.completeResolutionPresentation Y) f) := rfl
      simp only [Functor.comp_map, suspensionToStableOfPresentations_map, Functor.map_comp, hc]
      simp only [completeResolutionFunctor_map, eqToHom_map, Iso.trans_hom, eqToIso.hom,
        Functor.mapIso_hom, HomotopyCategory.isoOfHomotopyEquiv, Iso.app_hom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp]
      have hs : (HomotopyCategory.quotient C _).map (CompleteResolution.shiftMap (hE.liftMap f)) ≫
          (HomotopyCategory.quotient C _).map (hE.completeResolution Y).shiftComplexIso.hom =
          (HomotopyCategory.quotient C _).map (hE.completeResolution X).shiftComplexIso.hom ≫
            (HomotopyCategory.quotient C _).map ((hE.liftMap f)⟦(1 : ℤ)⟧') := by
        rw [← Functor.map_comp, ← Functor.map_comp,
          CompleteResolution.shiftMap_comp_shiftComplexIso_hom]
      rw [quotient_map_liftMap_cokernelMap_assoc, reassoc_of% hs,
        Functor.commShiftIso_hom_naturality_assoc])

/-- The functor from the stable category to the homotopy category intertwines stable
suspension with the shift by one. -/
noncomputable def stableSuspensionCompStableToHomotopyCategoryIso :
    hE.stableSuspension ⋙ hE.stableToHomotopyCategory ≅
      hE.stableToHomotopyCategory ⋙
        shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ) :=
  CategoryTheory.Quotient.natIsoLift _ <|
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hE.stableSuspensionIsoCompleteResolutionSuspension _ ≪≫
      hE.completeResolutionSuspensionCompIso ≪≫
      Functor.associator E.projectiveStableFunctor hE.stableToHomotopyCategory
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ))

/-- The functor from the stable category to the homotopy category commutes with the shifts. -/
@[instance_reducible]
noncomputable def stableToHomotopyCategoryCommShift :
    letI := hE.stableHasShift
    hE.stableToHomotopyCategory.CommShift ℤ :=
  hE.commShiftOfIntertwiningStableSuspensionShift _
    hE.stableSuspensionCompStableToHomotopyCategoryIso

/-- On an object of `C`, the shift comparison of the functor to the homotopy category is the
image of the stable shift identification, followed by the suspension comparisons. -/
theorem stableToHomotopyCategory_commShiftIso_one_hom_app (X : C) :
    letI := hE.stableHasShift
    letI := hE.stableToHomotopyCategoryCommShift
    (hE.stableToHomotopyCategory.commShiftIso (1 : ℤ)).hom.app (E.projectiveStableFunctor.obj X) =
      hE.stableToHomotopyCategory.map
          (hE.stableShiftFunctorOneIso.hom.app (E.projectiveStableFunctor.obj X)) ≫
        hE.stableToHomotopyCategory.map
          (hE.stableSuspensionIsoCompleteResolutionSuspension.hom.app X) ≫
        hE.completeResolutionSuspensionCompIso.hom.app X := by
  let := hE.stableHasShift
  rw [stableToHomotopyCategoryCommShift, commShiftOfIntertwiningStableSuspensionShift_iso_one]
  simp [stableSuspensionCompStableToHomotopyCategoryIso]

open Pretriangulated in
/-- The image of the standard triangle of a conflation is distinguished in the homotopy
category: it is isomorphic to the triangle of the degreewise split sequence of complete
resolutions given by the horseshoe lemma. -/
theorem stableToHomotopyCategory_map_stableConflationTriangle_mem_distTriang
    (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    letI := hE.stableToHomotopyCategoryCommShift
    hE.stableToHomotopyCategory.mapTriangle.obj (hE.stableConflationTriangle S hS) ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  let := hE.stableHasShift
  let := hE.stableToHomotopyCategoryCommShift
  rw [hE.stableConflationTriangle_eq_mk]
  have hS' : E.Conflation (ShortComplex.mk ((hE.completeResolutionIso S.X₁).hom ≫ S.f)
      (S.g ≫ (hE.completeResolutionIso S.X₃).inv) (by simp)) :=
    E.conflation_of_iso (ShortComplex.isoMk (hE.completeResolutionIso S.X₁).symm (Iso.refl _)
      (hE.completeResolutionIso S.X₃).symm (by simp) (by simp)) hS
  let h := CompleteResolution.horseshoe _ _ _ _ _ hS'
  let σ : ∀ n, ((ShortComplex.mk h.ι h.π h.ι_π).map (HomologicalComplex.eval C _ n)).Splitting :=
    fun n ↦ (h.split n).some
  let e₂ := CompleteResolution.homotopyEquiv (hE.completeResolution S.X₂) h.resolution
    (hE.completeResolutionIso S.X₂ ≪≫ h.iso.symm)
  let i₁ : hE.completeResolutionFunctor.obj S.X₁ ≅
      (HomotopyCategory.quotient C _).obj (hE.completeResolution S.X₁).complex :=
    eqToIso (hE.completeResolutionFunctor_obj S.X₁)
  let i₂ : hE.completeResolutionFunctor.obj S.X₂ ≅
      (HomotopyCategory.quotient C _).obj h.resolution.complex :=
    eqToIso (hE.completeResolutionFunctor_obj S.X₂) ≪≫ HomotopyCategory.isoOfHomotopyEquiv e₂
  let i₃ : hE.completeResolutionFunctor.obj S.X₃ ≅
      (HomotopyCategory.quotient C _).obj (hE.completeResolution S.X₃).complex :=
    eqToIso (hE.completeResolutionFunctor_obj S.X₃)
  refine isomorphic_distinguished _ (CochainComplex.trianglehOfDegreewiseSplit_distinguished
    _ σ) _ (Triangle.isoMk _ _ i₁ i₂ i₃ ?_ ?_ ?_) <;>
    dsimp only [Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_obj₃,
      Triangle.mk_mor₁, Triangle.mk_mor₂, Triangle.mk_mor₃,
      stableToHomotopyCategory_obj_projectiveStableFunctor_obj,
      CochainComplex.triangleOfDegreewiseSplit_obj₁, CochainComplex.triangleOfDegreewiseSplit_obj₂,
      CochainComplex.triangleOfDegreewiseSplit_obj₃, CochainComplex.triangleOfDegreewiseSplit_mor₁,
      CochainComplex.triangleOfDegreewiseSplit_mor₂, CochainComplex.triangleOfDegreewiseSplit_mor₃]
  · have key : (HomotopyCategory.quotient C _).map (hE.liftMap S.f) ≫
        (HomotopyCategory.quotient C _).map e₂.hom = (HomotopyCategory.quotient C _).map h.ι := by
      rw [← Functor.map_comp]
      exact (hE.quotient_map_eq_iff (hE.liftMap S.f ≫ e₂.hom) h.ι).2 (by
        rw [CompleteResolution.cyclesMap_comp, CompleteResolution.cyclesMap_homotopyEquiv_hom,
          cyclesMap_liftMap, h.cyclesMap_ι]
        simp)
    -- Restate the square with the objects of both triangles in their plain form.
    change hE.completeResolutionFunctor.map S.f ≫ i₂.hom =
      i₁.hom ≫ (HomotopyCategory.quotient C _).map h.ι
    simp only [completeResolutionFunctor_map, i₁, i₂, Iso.trans_hom, eqToIso.hom,
      HomotopyCategory.isoOfHomotopyEquiv, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, key]
  · have key : (HomotopyCategory.quotient C _).map (hE.liftMap S.g) =
        (HomotopyCategory.quotient C _).map e₂.hom ≫ (HomotopyCategory.quotient C _).map h.π := by
      rw [← Functor.map_comp]
      exact (hE.quotient_map_eq_iff (hE.liftMap S.g) (e₂.hom ≫ h.π)).2 (by
        rw [CompleteResolution.cyclesMap_comp, CompleteResolution.cyclesMap_homotopyEquiv_hom,
          cyclesMap_liftMap, h.cyclesMap_π]
        simp)
    -- Restate the square with the objects of both triangles in their plain form.
    change hE.completeResolutionFunctor.map S.g ≫ i₃.hom =
      i₂.hom ≫ (HomotopyCategory.quotient C _).map h.π
    simp only [completeResolutionFunctor_map, i₂, i₃, Iso.trans_hom, eqToIso.hom,
      HomotopyCategory.isoOfHomotopyEquiv, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, key]
  · -- The cycles map of the connecting cocycle, read in the shifted complete resolution.
    let r₁ := hE.completeResolution S.X₁
    let ψ : (hE.completeResolution S.X₃).complex ⟶ r₁.shift.complex :=
      CochainComplex.homOfDegreewiseSplit _ σ ≫ r₁.shiftComplexIso.inv
    let κ : (hE.completeResolution S.X₃).Z 0 ⟶ r₁.Z (0 + 1) := CompleteResolution.cyclesMap ψ
    let a : S.X₂ ⟶ r₁.X 0 := h.iso.inv ≫ h.resolution.ι 0 ≫ (σ 0).r
    have hfr : h.ι.f 0 ≫ (σ 0).r = 𝟙 _ := (σ 0).f_r
    have ha : S.f ≫ a = (hE.completeResolutionPresentation S.X₁).i := by
      have h₁ : S.f ≫ h.iso.inv = (hE.completeResolutionIso S.X₁).inv ≫
          CompleteResolution.cyclesMap h.ι := by
        rw [h.cyclesMap_ι]
        simp
      simp only [a, reassoc_of% h₁, CompleteResolution.cyclesMap_ι_assoc, hfr, Category.comp_id]
    have hψ : ψ.f 0 = (σ 0).s ≫ h.resolution.complex.d 0 (0 + 1) ≫ (σ (0 + 1)).r := by
      rw [HomologicalComplex.comp_f, CompleteResolution.shiftComplexIso_inv_f, Category.comp_id,
        CochainComplex.homOfDegreewiseSplit_f]
      -- The cocycle of a degreewise split sequence is defined componentwise by this formula.
      rfl
    have hκ : κ ≫ r₁.ι (0 + 1) = -((hE.completeResolution S.X₃).ι 0 ≫ (σ 0).s ≫
        h.resolution.d 0 ≫ (σ (0 + 1)).r) := by
      have := CompleteResolution.cyclesMap_ι ψ
      rw [hψ, CompleteResolution.complex_d] at this
      rw [← this]
      simp [κ]
    have hδ : S.g ≫ (hE.completeResolutionIso S.X₃).inv ≫ κ =
        a ≫ (hE.completeResolutionPresentation S.X₁).p := by
      rw [← cancel_mono (r₁.ι (0 + 1)), Category.assoc, Category.assoc, hκ, Preadditive.comp_neg,
        Preadditive.comp_neg, ← Category.assoc S.g, h.g_comp_connecting σ, neg_neg]
      simp [a, CompleteResolution.d_def]
      -- `r₁` is the chosen complete resolution of `S.X₁`.
      rfl
    have hconn := hE.projectiveStableFunctor_map_eq_connectingMap_comp hS
      (hE.completeResolutionPresentation S.X₁) a _ ha hδ
    have key : (HomotopyCategory.quotient C _).map
          (hE.liftMap ((hE.completeResolutionIso S.X₃).inv ≫ κ)) ≫
        (HomotopyCategory.quotient C _).map (hE.shiftHomotopyEquiv S.X₁).hom ≫
          (HomotopyCategory.quotient C _).map r₁.shiftComplexIso.hom =
        (HomotopyCategory.quotient C _).map (CochainComplex.homOfDegreewiseSplit _ σ) := by
      have h₁ : (HomotopyCategory.quotient C _).map
          (hE.liftMap ((hE.completeResolutionIso S.X₃).inv ≫ κ) ≫
            (hE.shiftHomotopyEquiv S.X₁).hom) = (HomotopyCategory.quotient C _).map ψ :=
        (hE.quotient_map_eq_iff _ ψ).2 (by
          rw [CompleteResolution.cyclesMap_comp, CompleteResolution.cyclesMap_homotopyEquiv_hom,
            cyclesMap_liftMap]
          simp [κ])
      rw [← Functor.map_comp_assoc, h₁, ← Functor.map_comp]
      simp [ψ]
    -- Restate the square with the objects of both triangles in their plain form.
    change (hE.stableToHomotopyCategory.map (E.projectiveStableFunctor.map (hE.connectingMap hS) ≫
        eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm ≫
          hE.stableShiftFunctorOneIso.inv.app (E.projectiveStableFunctor.obj S.X₁)) ≫
        (hE.stableToHomotopyCategory.commShiftIso (1 : ℤ)).hom.app
          (E.projectiveStableFunctor.obj S.X₁)) ≫ (shiftFunctor _ (1 : ℤ)).map i₁.hom =
      i₃.hom ≫ (HomotopyCategory.quotient C _).map (CochainComplex.homOfDegreewiseSplit _ σ) ≫
        ((HomotopyCategory.quotient C _).commShiftIso (1 : ℤ)).hom.app r₁.complex
    rw [stableToHomotopyCategory_commShiftIso_one_hom_app]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc hE.stableToHomotopyCategory
      (hE.stableShiftFunctorOneIso.inv.app _), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [stableSuspensionIsoCompleteResolutionSuspension, completeResolutionSuspensionCompIso,
      NatIso.ofComponents_hom_app, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, HomotopyCategory.isoOfHomotopyEquiv, Iso.app_hom]
    rw [← Functor.map_comp_assoc, ← hconn,
      stableToHomotopyCategory_map_projectiveStableFunctor_map, completeResolutionFunctor_map]
    simp only [i₁, i₃, eqToIso.hom, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [reassoc_of% key]

/-- **The complete-resolution functor from the stable category to the homotopy category is a
triangle functor.** -/
theorem stableToHomotopyCategory_isTriangulated :
    letI := hE.stableHasShift
    letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE.stableToHomotopyCategoryCommShift
    hE.stableToHomotopyCategory.IsTriangulated := by
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.stableToHomotopyCategoryCommShift
  constructor
  intro T hT
  rw [stablePretriangulated_distinguishedTriangles, mem_stableDistinguishedTriangles_iff] at hT
  obtain ⟨S, hS, ⟨e⟩⟩ := hT
  exact Pretriangulated.isomorphic_distinguished _
    (hE.stableToHomotopyCategory_map_stableConflationTriangle_mem_distTriang S hS) _
    (hE.stableToHomotopyCategory.mapTriangle.mapIso e)

instance : hE.stableToHomotopyCategory.Full :=
  Functor.Full.of_iso hE.stableToCompleteResolutionHomotopyCategoryCompιIso

/-- `K_ac(P)` is the essential image of the complete-resolution functor. -/
theorem completeResolutionComplex_eq_essImage :
    E.completeResolutionComplex = hE.stableToHomotopyCategory.essImage := by
  ext K
  rw [completeResolutionComplex_iff]
  constructor
  · rintro ⟨r, ⟨e⟩⟩
    exact ⟨E.projectiveStableFunctor.obj (r.Z 0), ⟨eqToIso (hE.completeResolutionFunctor_obj _) ≪≫
      HomotopyCategory.isoOfHomotopyEquiv
        (CompleteResolution.homotopyEquiv _ r (hE.completeResolutionIso (r.Z 0))) ≪≫ e.symm⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨hE.completeResolution X.as,
      ⟨e.symm ≪≫ eqToIso (hE.completeResolutionFunctor_obj X.as)⟩⟩

include hE in
/-- **`K_ac(P)` is a triangulated subcategory of the homotopy category.** It is closed under
shifts and cones, being the essential image of a full triangle functor. -/
theorem completeResolutionComplex_isTriangulated :
    ObjectProperty.IsTriangulated E.completeResolutionComplex := by
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.stableToHomotopyCategoryCommShift
  have := hE.stableToHomotopyCategory_isTriangulated
  rw [hE.completeResolutionComplex_eq_essImage]
  infer_instance

/-- The functor from the stable category to `K_ac(P)` commutes with the shifts, compatibly with
the inclusion of `K_ac(P)` into the homotopy category. -/
@[instance_reducible]
noncomputable def stableToCompleteResolutionHomotopyCategoryCommShift :
    letI := hE.stableHasShift
    letI := hE.stableToHomotopyCategoryCommShift
    letI := hE.completeResolutionComplex_isTriangulated
    hE.stableToCompleteResolutionHomotopyCategory.CommShift ℤ := by
  let := hE.stableHasShift
  let := hE.stableToHomotopyCategoryCommShift
  have := hE.completeResolutionComplex_isTriangulated
  exact Functor.CommShift.ofComp hE.stableToCompleteResolutionHomotopyCategoryCompιIso ℤ

/-- **The equivalence between the stable category and `K_ac(P)` is a triangle functor**, for
Happel's triangulation of the stable category and the triangulation of `K_ac(P)` as a
triangulated subcategory of the homotopy category. -/
theorem stableToCompleteResolutionHomotopyCategory_isTriangulated :
    letI := hE.stableHasShift
    letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE.stableToHomotopyCategoryCommShift
    letI := hE.completeResolutionComplex_isTriangulated
    letI := hE.stableToCompleteResolutionHomotopyCategoryCommShift
    hE.stableToCompleteResolutionHomotopyCategory.IsTriangulated := by
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.stableToHomotopyCategoryCommShift
  have := hE.completeResolutionComplex_isTriangulated
  let := hE.stableToCompleteResolutionHomotopyCategoryCommShift
  have := hE.stableToHomotopyCategory_isTriangulated
  have := Functor.CommShift.ofComp_compatibility
    hE.stableToCompleteResolutionHomotopyCategoryCompιIso ℤ
  constructor
  intro T hT
  rw [← E.completeResolutionComplex.ι.map_distinguished_iff]
  exact Pretriangulated.isomorphic_distinguished _
    (hE.stableToHomotopyCategory.map_distinguished T hT) _
    ((Functor.mapTriangleCompIso _ _).symm.app T ≪≫
      (Functor.mapTriangleIso hE.stableToCompleteResolutionHomotopyCategoryCompιIso).app T)

end IsFrobenius

end ExactStructure

end TauCeti
