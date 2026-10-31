/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact functors preserving injective objects and injective resolutions

An additive functor `F : C ⥤ D` which preserves homology and injective objects sends an injective
resolution `I` of `Z` to an injective resolution `F.mapInjectiveResolution I` of `F.obj Z`, whose
complex is `F` applied to the complex of `I`. This is the dual of Mathlib's
`CategoryTheory.Functor.mapProjectiveResolution`.

Consequently, choosing injective resolutions commutes with `F` up to homotopy: the functor
`injectiveResolutions C ⋙ F.mapHomotopyCategory _` is naturally isomorphic to
`F ⋙ injectiveResolutions D` (`CategoryTheory.Functor.injectiveResolutionsCompIso`). This is what
makes right derived functors commute with such functors.
-/

public section

open CategoryTheory Limits

universe v v' u u'

namespace CategoryTheory.Functor

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [CategoryWithHomology D]

/-- An additive functor `F` which preserves homology and sends injective objects to injective
objects sends an injective resolution of `Z` to an injective resolution of `F.obj Z`.

The body is exposed so that the complex of the image is definitionally `F` applied to the complex
of `I`, as `injectiveResolutionsCompIso` requires. -/
@[expose, simps cocomplex]
noncomputable def mapInjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology] {Z : C} (I : InjectiveResolution Z) :
    InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := PreservesInjectiveObjects.injective_obj (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F _ _).inv.app _ ≫
    (F.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

/-- In degree zero, the coaugmentation of `F.mapInjectiveResolution I` is `F` applied to that
of `I`. -/
@[simp]
lemma mapInjectiveResolution_ι_f_zero (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology] {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I).ι.f 0 = F.map (I.ι.f 0) := by
  simp [mapInjectiveResolution]

end

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]

/-- Choosing injective resolutions commutes, up to homotopy, with an additive functor preserving
homology and injective objects: `F` applied to the chosen resolution of `X` is homotopy
equivalent to the chosen resolution of `F.obj X`, naturally in `X`. -/
noncomputable def injectiveResolutionsCompIso :
    injectiveResolutions C ⋙ F.mapHomotopyCategory _ ≅ F ⋙ injectiveResolutions D :=
  NatIso.ofComponents
    -- `F.mapHomotopyCategory` sends the class of a complex to the class of its image under `F`
    (fun X ↦ (F.mapInjectiveResolution (injectiveResolution X)).iso.symm)
    (fun {X Y} f ↦ by
      -- `(injectiveResolutions C).map f` is the class of `desc f`, and `F.mapHomotopyCategory`
      -- sends it to the class of `F` applied to `desc f`, a lift of `F.map f`
      exact (InjectiveResolution.iso_inv_naturality (F.map f)
        (F.mapInjectiveResolution (injectiveResolution X))
        (F.mapInjectiveResolution (injectiveResolution Y))
        ((F.mapHomologicalComplex _).map (InjectiveResolution.desc f _ _))
        (by
          rw [mapInjectiveResolution_ι_f_zero, mapInjectiveResolution_ι_f_zero,
            mapHomologicalComplex_map_f]
          -- `F.map_comp` is applied by unification: the source of `I.ι.f 0` is `X` only up to
          -- unfolding `CochainComplex.single₀`
          exact (F.map_comp _ _).symm.trans
            ((congrArg F.map (InjectiveResolution.desc_commutes_zero f _ _)).trans
              (F.map_comp _ _)))).symm)

/-- The comparison `injectiveResolutionsCompIso` at `X` is the homotopy equivalence between `F`
applied to the chosen resolution of `X` and the chosen resolution of `F.obj X`. -/
@[simp]
lemma injectiveResolutionsCompIso_hom_app (X : C) :
    (F.injectiveResolutionsCompIso).hom.app X =
      (F.mapInjectiveResolution (injectiveResolution X)).iso.inv :=
  (rfl)

end CategoryTheory.Functor
