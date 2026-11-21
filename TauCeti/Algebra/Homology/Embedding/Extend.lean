/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Functoriality and naturality of extension along complex-shape embeddings

Let `e : c.Embedding c'` be an embedding of complex shapes. This file records two naturality
compatibilities for Mathlib's extension-by-zero functor `e.extendFunctor`:

* `ComplexShape.Embedding.mapExtendIso` and
  `ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`: for any functor `F : C ⥤ D`
  preserving zero morphisms between categories with zero objects and zero morphisms,
  `e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅ F.mapHomologicalComplex c ⋙ e.extendFunctor D`
  (and objectwise `(F.mapHomologicalComplex c').obj (K.extend e) ≅
  ((F.mapHomologicalComplex c).obj K).extend e`), with component formulas in the image of `e.f`.
* `ComplexShape.Embedding.extendSingleIso_hom_naturality` and
  `ComplexShape.Embedding.extendSingleIso_inv_naturality`: naturality of Mathlib's
  `HomologicalComplex.extendSingleIso` in the object argument.

## References

* Mathlib's `Mathlib/Algebra/Homology/Embedding/Extend.lean`, whose `extend.X` / `extendOpIso`
  pattern is followed here.
* `TauCeti/Algebra/Homology/Embedding/Restriction/Basic.lean`, the counterpart for
  `e.restrictionFunctor`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject

universe v₁ v₂ u₁ u₂

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

section MapExtend

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]

/-- Component isomorphism `F(extend.X K o) ≅ extend.X (F(K)) o` on `Option ι`. -/
private def mapExtendXIso (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) :
    ∀ o : Option ι, F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o
  | some _ =>
    F.mapIso (HomologicalComplex.extend.XIso K rfl) ≪≫
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) rfl).symm
  | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero D)

private lemma mapExtendXIso_hom_d (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (o₁ o₂ : Option ι) :
    (mapExtendXIso F K o₁).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) o₁ o₂ =
      F.map (HomologicalComplex.extend.d K o₁ o₂) ≫ (mapExtendXIso F K o₂).hom := by
  cases o₁ with
  | none =>
    simp [HomologicalComplex.extend.d_none_eq_zero]
  | some i =>
    cases o₂ with
    | none =>
      simp [HomologicalComplex.extend.d_none_eq_zero']
    | some j =>
      rw [HomologicalComplex.extend.d_eq K rfl rfl,
        HomologicalComplex.extend.d_eq ((F.mapHomologicalComplex c).obj K) rfl rfl]
      simp [mapExtendXIso]

private lemma mapExtendXIso_hom_mapX (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (o : Option ι) :
    F.map (HomologicalComplex.extend.mapX φ o) ≫ (mapExtendXIso F L o).hom =
      (mapExtendXIso F K o).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map φ) o := by
  cases o with
  | none =>
    exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
  | some i =>
    rw [HomologicalComplex.extend.mapX_some φ rfl,
      HomologicalComplex.extend.mapX_some ((F.mapHomologicalComplex c).map φ) rfl]
    simp [mapExtendXIso]

/-- Objectwise isomorphism commuting extension along a complex-shape embedding `e` with
termwise application of a functor `F` preserving zero morphisms. -/
def mapExtendIso (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' ↦ mapExtendXIso F K (e.r i'))
    (fun i' j' _ ↦ mapExtendXIso_hom_d F K (e.r i') (e.r j'))

private lemma mapExtendXIso_hom_eq_some (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {o : Option ι} {i : ι} (hr : o = some i) :
    (mapExtendXIso F K o).hom =
      F.map (HomologicalComplex.extend.XIso K hr).hom ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) hr).inv := by
  subst hr
  rfl

private lemma mapExtendXIso_inv_eq_some (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {o : Option ι} {i : ι} (hr : o = some i) :
    (mapExtendXIso F K o).inv =
      (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) hr).hom ≫
        F.map (HomologicalComplex.extend.XIso K hr).inv := by
  subst hr
  rfl

/-- In a degree `i' = e.f i` in the image of `e`, the forward component of `mapExtendIso`
identifies `F((K.extend e).X i')` with `((F(K)).extend e).X i'` via
`HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma mapExtendIso_hom_f (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.mapExtendIso F K).hom.f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  mapExtendXIso_hom_eq_some F K (e.r_eq_some h)

/-- In a degree `i' = e.f i` in the image of `e`, the inverse component of `mapExtendIso`
identifies `((F(K)).extend e).X i'` with `F((K.extend e).X i')` via
`HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma mapExtendIso_inv_f (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    (e.mapExtendIso F K).inv.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv :=
  mapExtendXIso_inv_eq_some F K (e.r_eq_some h)

/-- Naturality of `mapExtendIso` in morphisms of complexes. -/
@[reassoc]
lemma mapExtendIso_hom_naturality (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) :
    (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap φ e) ≫
        (e.mapExtendIso F L).hom =
      (e.mapExtendIso F K).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  exact mapExtendXIso_hom_mapX F φ (e.r i')

/-- Extending along a complex-shape embedding `e` commutes naturally with termwise application of a
functor `F` preserving zero morphisms. -/
def extendFunctorCompMapHomologicalComplexIso (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (e.mapExtendIso F) (fun φ ↦ e.mapExtendIso_hom_naturality F φ)

/-- In a degree `i' = e.f i` in the image of `e`, the forward component of
`extendFunctorCompMapHomologicalComplexIso` identifies `F((K.extend e).X i')` with
`((F(K)).extend e).X i'` via `HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma extendFunctorCompMapHomologicalComplexIso_hom_app_f (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    ((e.extendFunctorCompMapHomologicalComplexIso F).hom.app K).f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  e.mapExtendIso_hom_f F K h

/-- In a degree `i' = e.f i` in the image of `e`, the inverse component of
`extendFunctorCompMapHomologicalComplexIso` identifies `((F(K)).extend e).X i'` with
`F((K.extend e).X i')` via `HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma extendFunctorCompMapHomologicalComplexIso_inv_app_f (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    ((e.extendFunctorCompMapHomologicalComplexIso F).inv.app K).f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv :=
  e.mapExtendIso_inv_f F K h

end MapExtend

section ExtendSingle

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  [DecidableEq ι] [DecidableEq ι']

/-- Naturality of the inverse of `HomologicalComplex.extendSingleIso` in the object argument. -/
@[reassoc]
lemma extendSingleIso_inv_naturality (e : c.Embedding c') {X Y : C} (f : X ⟶ Y)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.single C c' i').map f ≫
        (HomologicalComplex.extendSingleIso e Y i i' h).inv =
      (HomologicalComplex.extendSingleIso e X i i' h).inv ≫
        HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map f) e := by
  ext
  simp [HomologicalComplex.extendSingleIso_inv_f, HomologicalComplex.extendMap_f _ e h,
    HomologicalComplex.single_map_f_self]

/-- Naturality of the forward morphism of `HomologicalComplex.extendSingleIso` in the object
argument. -/
@[reassoc]
lemma extendSingleIso_hom_naturality (e : c.Embedding c') {X Y : C} (f : X ⟶ Y)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map f) e ≫
        (HomologicalComplex.extendSingleIso e Y i i' h).hom =
      (HomologicalComplex.extendSingleIso e X i i' h).hom ≫
        (HomologicalComplex.single C c' i').map f := by
  rw [← cancel_epi (HomologicalComplex.extendSingleIso e X i i' h).inv,
    ← extendSingleIso_inv_naturality_assoc e f h]
  simp

end ExtendSingle

end ComplexShape.Embedding
