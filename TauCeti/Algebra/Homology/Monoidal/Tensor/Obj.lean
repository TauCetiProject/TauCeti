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

Its terms are `X ⊗ P.X n` (`HomologicalComplex.objTensor_obj_X`), its differentials `X ◁ P.d i j`
(`HomologicalComplex.objTensor_obj_d`), and it sends `f` to the maps `f ▷ P.X n`
(`HomologicalComplex.objTensor_map_f`). Evaluated in degree `n`, it is `tensorRight (P.X n)`
(`HomologicalComplex.objTensorCompEvalIso`). In a preadditive monoidal category it is additive.
-/

public section

noncomputable section

namespace HomologicalComplex

open CategoryTheory Limits MonoidalCategory

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [MonoidalCategory C]
  [∀ X : C, (tensorLeft X).PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}
  (P : HomologicalComplex C c)

-- The body is exposed: the statements of the component lemmas below (for instance that the
-- differential of `X ⊗ P` is `X ◁ P.d i j`) are only well typed when the terms of `X ⊗ P` are
-- `X ⊗ P.X n` by definition, and `objTensor P` applied to `X` is by definition Mathlib's
-- prolongation of `tensorLeft X`, on which `ProjectiveResolution.isoLeftDerivedObj` is stated.
/-- The functor `X ↦ X ⊗ P` from `C` to complexes, tensoring every term of the complex `P` on the
left with `X`. -/
@[expose]
def objTensor : C ⥤ HomologicalComplex C c where
  obj X := ((tensorLeft X).mapHomologicalComplex c).obj P
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft C).map f) c).app P
  map_id X := by
    rw [(tensoringLeft C).map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp f g := by
    rw [(tensoringLeft C).map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- The term of `X ⊗ P` in degree `n` is `X ⊗ P.X n`. -/
@[simp]
lemma objTensor_obj_X (X : C) (n : ι) : (P.objTensor.obj X).X n = X ⊗ P.X n :=
  (rfl)

/-- The differential of `X ⊗ P` is `X` whiskered with the differential of `P`. -/
@[simp]
lemma objTensor_obj_d (X : C) (i j : ι) : (P.objTensor.obj X).d i j = X ◁ P.d i j :=
  (rfl)

/-- The map `X ⊗ P ⟶ Y ⊗ P` induced by `f : X ⟶ Y` is `f ▷ P.X n` in degree `n`. -/
@[simp]
lemma objTensor_map_f {X Y : C} (f : X ⟶ Y) (n : ι) : (P.objTensor.map f).f n = f ▷ P.X n :=
  (rfl)

/-- `X ⊗ P` is Mathlib's prolongation of `tensorLeft X` to complexes, applied to `P`. -/
def objTensorObjIso (X : C) : P.objTensor.obj X ≅ ((tensorLeft X).mapHomologicalComplex c).obj P :=
  Iso.refl _

/-- The comparison `objTensorObjIso` is the identity in each degree. -/
@[simp]
lemma objTensorObjIso_hom_f (X : C) (n : ι) : (P.objTensorObjIso X).hom.f n = 𝟙 (X ⊗ P.X n) :=
  (rfl)

/-- The inverse of the comparison `objTensorObjIso` is the identity in each degree. -/
@[simp]
lemma objTensorObjIso_inv_f (X : C) (n : ι) : (P.objTensorObjIso X).inv.f n = 𝟙 (X ⊗ P.X n) :=
  (rfl)

/-- The comparison `objTensorObjIso` is natural: the map induced by `f` is the prolongation of
`(tensoringLeft C).map f` evaluated at `P`. -/
@[reassoc]
lemma objTensor_map_objTensorObjIso_hom {X Y : C} (f : X ⟶ Y) :
    P.objTensor.map f ≫ (P.objTensorObjIso Y).hom =
      (P.objTensorObjIso X).hom ≫
        (NatTrans.mapHomologicalComplex ((tensoringLeft C).map f) c).app P :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- Evaluated in degree `n`, the functor `X ↦ X ⊗ P` is `tensorRight (P.X n)`. -/
def objTensorCompEvalIso (n : ι) : P.objTensor ⋙ eval C c n ≅ tensorRight (P.X n) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦
    (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of `objTensorCompEvalIso` are identities of `X ⊗ P.X n`. -/
@[simp]
lemma objTensorCompEvalIso_hom_app (n : ι) (X : C) :
    (P.objTensorCompEvalIso n).hom.app X = 𝟙 (X ⊗ P.X n) :=
  (rfl)

/-- In a preadditive monoidal category, `X ↦ X ⊗ P` is additive. -/
instance {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]
    (P : HomologicalComplex C c) : P.objTensor.Additive where
  map_add {_ _ f g} := by
    ext
    exact MonoidalPreadditive.add_whiskerRight f g

end HomologicalComplex
