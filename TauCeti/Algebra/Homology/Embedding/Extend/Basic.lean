/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.MapExtend

/-!
# Functoriality and naturality of extension along complex-shape embeddings

Let `e : c.Embedding c'` be an embedding of complex shapes. This file records naturality
compatibilities building on `HomologicalComplex.mapExtendIso` and
`HomologicalComplex.extendSingleIso`:

* `HomologicalComplex.mapExtendIso_inv_f` and `HomologicalComplex.mapExtendIso_hom_naturality`:
  inverse component formula and naturality of `HomologicalComplex.mapExtendIso`.
* `ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`: for any functor `F : C ⥤ D`
  preserving zero morphisms between categories with zero objects and zero morphisms,
  `e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅ F.mapHomologicalComplex c ⋙ e.extendFunctor D`,
  with component formulas in the image of `e.f`.
* `ComplexShape.Embedding.extendSingleIso_hom_naturality` and
  `ComplexShape.Embedding.extendSingleIso_inv_naturality`: naturality of Mathlib's
  `HomologicalComplex.extendSingleIso` in the object argument.

## References

* Mathlib's `Mathlib/Algebra/Homology/Embedding/Extend.lean`.
* `TauCeti/Algebra/Homology/Embedding/MapExtend.lean` for `HomologicalComplex.mapExtendIso`.
* `TauCeti/Algebra/Homology/Embedding/Restriction/Basic.lean`, the counterpart for
  `e.restrictionFunctor`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

section MapExtend

namespace HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]

/-- In a degree `i' = e.f i` in the image of `e`, the inverse component of
`HomologicalComplex.mapExtendIso` identifies `((F(K)).extend e).X i'` with `F((K.extend e).X i')`
via `HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma mapExtendIso_inv_f (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (K : HomologicalComplex C c) (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') :
    (mapExtendIso F K e).inv.f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv := by
  have hid : (mapExtendIso F K e).hom.f i' ≫ (mapExtendIso F K e).inv.f i' = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rw [← cancel_epi ((mapExtendIso F K e).hom.f i'), hid, mapExtendIso_hom_f F K e h]
  simp

/-- Naturality of `HomologicalComplex.mapExtendIso` in morphisms of complexes. -/
@[reassoc]
lemma mapExtendIso_hom_naturality (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (mapExtendIso F L e).hom =
      (mapExtendIso F K e).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i'
  by_cases h : ∃ i, e.f i = i'
  · rcases h with ⟨i, hi⟩
    simp [mapExtendIso_hom_f _ _ e hi, extendMap_f φ e hi,
      extendMap_f ((F.mapHomologicalComplex c).map φ) e hi]
  · exact (F.map_isZero (K.isZero_extend_X e i' fun i hi ↦ h ⟨i, hi⟩)).eq_of_src _ _

end HomologicalComplex

namespace ComplexShape.Embedding

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]

/-- Extending along a complex-shape embedding `e` commutes naturally with termwise application of a
functor `F` preserving zero morphisms. -/
def extendFunctorCompMapHomologicalComplexIso (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] :
    e.extendFunctor C ⋙ F.mapHomologicalComplex c' ≅
      F.mapHomologicalComplex c ⋙ e.extendFunctor D :=
  NatIso.ofComponents (fun K ↦ HomologicalComplex.mapExtendIso F K e)
    (fun φ ↦ HomologicalComplex.mapExtendIso_hom_naturality F φ e)

/-- In a degree `i' = e.f i` in the image of `e`, the forward component of
`extendFunctorCompMapHomologicalComplexIso` identifies `F((K.extend e).X i')` with
`((F(K)).extend e).X i'` via `HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma extendFunctorCompMapHomologicalComplexIso_hom_app_f (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    ((e.extendFunctorCompMapHomologicalComplexIso F).hom.app K).f i' =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  HomologicalComplex.mapExtendIso_hom_f F K e h

/-- In a degree `i' = e.f i` in the image of `e`, the inverse component of
`extendFunctorCompMapHomologicalComplexIso` identifies `((F(K)).extend e).X i'` with
`F((K.extend e).X i')` via `HomologicalComplex.extendXIso`. -/
@[reassoc]
lemma extendFunctorCompMapHomologicalComplexIso_inv_app_f (e : c.Embedding c') (F : C ⥤ D)
    [F.PreservesZeroMorphisms] (K : HomologicalComplex C c) {i : ι} {i' : ι'} (h : e.f i = i') :
    ((e.extendFunctorCompMapHomologicalComplexIso F).inv.app K).f i' =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map (K.extendXIso e h).inv :=
  HomologicalComplex.mapExtendIso_inv_f F K e h

end ComplexShape.Embedding

end MapExtend

namespace ComplexShape.Embedding

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
