/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Ind
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.RingHomProperties

/-!
# Descent of finitely presented algebras

A finitely presented algebra over a filtered colimit of commutative rings is a pushout
of a finitely presented algebra over one stage. Lift the finitely many coefficients of a
native algebra presentation to a common stage, then use its model and tensor equivalence.
This is the affine object-descent step for finitely presented schemes.

## Main results

* `TauCeti.CommRingCat.exists_isPushout_of_finitePresentation`: descent to a stage, with
  independently sized indexing categories.
* `RingHom.FinitePresentation.preIndSpreads`: the instance for morphism-property consumers.
-/

public section

universe categoryHom categoryObj ringUniverse

open CategoryTheory Limits

namespace TauCeti.CommRingCat

/-- A finitely presented algebra over a filtered colimit is the pushout of a finitely presented
algebra over one stage. -/
theorem exists_isPushout_of_finitePresentation
    {Index : Type categoryObj} [Category.{categoryHom} Index] [IsFiltered Index]
    (diagram : Index ⥤ CommRingCat.{ringUniverse}) (cocone : Cocone diagram)
    [PreservesColimit diagram (forget CommRingCat)] (colimit : IsColimit cocone)
    {T : CommRingCat.{ringUniverse}} (f : cocone.pt ⟶ T) (hfp : f.hom.FinitePresentation) :
    ∃ (stage : Index) (B : CommRingCat.{ringUniverse})
      (fᵢ : diagram.obj stage ⟶ B) (_ : fᵢ.hom.FinitePresentation)
      (g : B ⟶ T), IsPushout (cocone.ι.app stage) fᵢ f g := by
  classical
  let := f.hom.toAlgebra
  have : Algebra.FinitePresentation cocone.pt T := hfp
  let P := Algebra.Presentation.ofFinitePresentation cocone.pt T
  let : Fintype P.coeffs := P.finite_coeffs.fintype
  -- Only the finite coefficient set must be lifted; the native model handles the relations.
  have hsurj : ∀ r : cocone.pt, ∃ (j : Index) (x : diagram.obj j),
      (cocone.ι.app j).hom x = r := by
    simpa only [Functor.mapCocone_pt, Functor.mapCocone_ι_app, CommRingCat.forget_map_apply]
      using! Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget _) colimit)
  choose j x hx using fun r : P.coeffs ↦ hsurj r
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let : Algebra (diagram.obj i) cocone.pt := (cocone.ι.app i).hom.toAlgebra
  let : Algebra (diagram.obj i) T := (f.hom.comp (cocone.ι.app i).hom).toAlgebra
  have : IsScalarTower (diagram.obj i) cocone.pt T :=
    IsScalarTower.of_algebraMap_eq' (R := diagram.obj i) (S := cocone.pt) (A := T) rfl
  have : P.HasCoeffs (diagram.obj i) := by
    constructor
    intro r hr
    obtain ⟨hji⟩ := hi (Finset.mem_image_of_mem j (Finset.mem_univ (⟨r, hr⟩ : P.coeffs)))
    refine ⟨diagram.map hji (x ⟨r, hr⟩), ?_⟩
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      using (congrArg (fun g ↦ g.hom (x ⟨r, hr⟩)) (cocone.w hji)).trans (hx ⟨r, hr⟩)
  let B := P.ModelOfHasCoeffs (diagram.obj i)
  let e := P.tensorModelOfHasCoeffsEquiv (diagram.obj i)
  refine ⟨i, CommRingCat.of B, CommRingCat.ofHom (algebraMap (diagram.obj i) B),
    RingHom.finitePresentation_algebraMap.mpr inferInstance,
    CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_⟩
  refine (CommRingCat.isPushout_tensorProduct (diagram.obj i) cocone.pt B).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    (by simp [RingHom.algebraMap_toAlgebra]) (by simp) ?_
    (CommRingCat.ofHom_comp _ _).symm
  ext r
  simpa [RingHom.algebraMap_toAlgebra] using e.commutes r

end TauCeti.CommRingCat

namespace RingHom

/-- Finitely presented ring maps descend out of small filtered colimits. -/
instance FinitePresentation.preIndSpreads :
    MorphismProperty.PreIndSpreads.{ringUniverse}
      (toMorphismProperty FinitePresentation : MorphismProperty CommRingCat.{ringUniverse}) where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    obtain ⟨j, B, f', hf', g, h⟩ :=
      TauCeti.CommRingCat.exists_isPushout_of_finitePresentation D c hc f hf
    exact ⟨j, B, f', g, h, hf'⟩

end RingHom
