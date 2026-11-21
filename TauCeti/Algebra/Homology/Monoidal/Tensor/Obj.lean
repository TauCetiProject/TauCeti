/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensoring a complex termwise with an object

Let `C` be a monoidal category with zero morphisms in which tensoring on the left with any object
preserves zero morphisms, and let `P` be a homological complex in `C`. Tensoring every term of
`P` on the left with an object `X` gives a complex `X ⊗ P`, and this is functorial in `X`: it is the
functor `HomologicalComplex.objTensor P : C ⥤ HomologicalComplex C c`. It is assembled from
Mathlib's prolongation of functors and natural transformations to complexes: on objects it is
`Functor.mapHomologicalComplex` of `tensorLeft X` applied to `P`, and on morphisms
`NatTrans.mapHomologicalComplex` of `(tensoringLeft C).map f` evaluated at `P`.

Its terms are identified with `X ⊗ P.X n` (`HomologicalComplex.objTensorXIso`), under which its
differentials are `X ◁ P.d i j` (`HomologicalComplex.objTensorXIso_inv_d`) and it sends `f` to the
maps `f ▷ P.X n` (`HomologicalComplex.objTensorXIso_inv_map_f`). It is identified with Mathlib's
prolongation of `tensorLeft X` applied to `P` (`HomologicalComplex.objTensorObjIso`), naturally in
`X`. Evaluated in degree `n`, it is `tensorRight (P.X n)`
(`HomologicalComplex.objTensorCompEvalIso`). In a preadditive monoidal category it is additive.
-/

public section

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits MonoidalCategory

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [MonoidalCategory C]
  [∀ X : C, (tensorLeft X).PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}
  (P : HomologicalComplex C c)

/-- The functor `X ↦ X ⊗ P` from `C` to complexes, tensoring every term of the complex `P` on the
left with `X`. Its terms, differentials and maps are described through the identifications
`HomologicalComplex.objTensorXIso` of its terms with `X ⊗ P.X n`, and it is compared with Mathlib's
prolongation of `tensorLeft X` by `HomologicalComplex.objTensorObjIso`. -/
def objTensor : C ⥤ HomologicalComplex C c where
  obj X := ((tensorLeft X).mapHomologicalComplex c).obj P
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft C).map f) c).app P
  map_id X := by
    rw [(tensoringLeft C).map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp f g := by
    rw [(tensoringLeft C).map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- The term of `X ⊗ P` in degree `n` is `X ⊗ P.X n`. -/
def objTensorXIso (X : C) (n : ι) : (P.objTensor.obj X).X n ≅ X ⊗ P.X n :=
  -- by definition of `objTensor`
  Iso.refl _

/-- The differential of `X ⊗ P` is `X` whiskered with the differential of `P`. -/
@[reassoc (attr := simp)]
lemma objTensorXIso_inv_d (X : C) (i j : ι) :
    (P.objTensorXIso X i).inv ≫ (P.objTensor.obj X).d i j =
      X ◁ P.d i j ≫ (P.objTensorXIso X j).inv :=
  -- both identifications are identities, and the differential is `X ◁ P.d i j` by definition
  (Category.id_comp _).trans (Category.comp_id _).symm

/-- The map `X ⊗ P ⟶ Y ⊗ P` induced by `f : X ⟶ Y` is `f ▷ P.X n` in degree `n`. -/
@[reassoc (attr := simp)]
lemma objTensorXIso_inv_map_f {X Y : C} (f : X ⟶ Y) (n : ι) :
    (P.objTensorXIso X n).inv ≫ (P.objTensor.map f).f n = f ▷ P.X n ≫ (P.objTensorXIso Y n).inv :=
  -- both identifications are identities, and the map is `f ▷ P.X n` by definition
  (Category.id_comp _).trans (Category.comp_id _).symm

/-- `X ⊗ P` is Mathlib's prolongation of `tensorLeft X` to complexes, applied to `P`. -/
def objTensorObjIso (X : C) : P.objTensor.obj X ≅ ((tensorLeft X).mapHomologicalComplex c).obj P :=
  -- by definition of `objTensor`
  Iso.refl _

/-- In each degree, the comparison `objTensorObjIso` is the identification `objTensorXIso`. -/
@[simp]
lemma objTensorObjIso_hom_f (X : C) (n : ι) :
    (P.objTensorObjIso X).hom.f n = (P.objTensorXIso X n).hom :=
  (rfl)

/-- In each degree, the inverse of `objTensorObjIso` is the inverse of `objTensorXIso`. -/
@[simp]
lemma objTensorObjIso_inv_f (X : C) (n : ι) :
    (P.objTensorObjIso X).inv.f n = (P.objTensorXIso X n).inv :=
  (rfl)

/-- The comparison `objTensorObjIso` is natural: the map induced by `f` is the prolongation of
`(tensoringLeft C).map f` evaluated at `P`. -/
@[reassoc]
lemma objTensor_map_objTensorObjIso_hom {X Y : C} (f : X ⟶ Y) :
    P.objTensor.map f ≫ (P.objTensorObjIso Y).hom =
      (P.objTensorObjIso X).hom ≫
        (NatTrans.mapHomologicalComplex ((tensoringLeft C).map f) c).app P :=
  -- both comparisons are identities, and `objTensor P` acts on maps in this way by definition
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- Evaluated in degree `n`, the functor `X ↦ X ⊗ P` is `tensorRight (P.X n)`. -/
def objTensorCompEvalIso (n : ι) : P.objTensor ⋙ eval C c n ≅ tensorRight (P.X n) :=
  NatIso.ofComponents (fun X ↦ P.objTensorXIso X n) fun f ↦ by
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
    exact P.objTensorXIso_inv_map_f f n

/-- The components of `objTensorCompEvalIso` are the identifications `objTensorXIso`. -/
@[simp]
lemma objTensorCompEvalIso_hom_app (n : ι) (X : C) :
    (P.objTensorCompEvalIso n).hom.app X = (P.objTensorXIso X n).hom :=
  (rfl)

/-- In a preadditive monoidal category, `X ↦ X ⊗ P` is additive. -/
instance {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
    (P : HomologicalComplex C c) : P.objTensor.Additive where
  map_add {_ _ f g} := by
    ext n
    rw [← cancel_epi (P.objTensorXIso _ n).inv, HomologicalComplex.add_f_apply,
      Preadditive.comp_add, objTensorXIso_inv_map_f, objTensorXIso_inv_map_f,
      objTensorXIso_inv_map_f, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

end HomologicalComplex
