/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Commuting identifications and naturality of extended complexes

Let `e : c.Embedding c'` be an embedding of complex shapes and `K` a complex of shape `c`. In a
degree `e.f i` the extended complex `K.extend e` is identified with `K.X i`
(`HomologicalComplex.extendXIso`). Mathlib describes the differential of `K.extend e` and the
extension of a chain map by conjugating with these identifications
(`HomologicalComplex.extend_d_eq`, `HomologicalComplex.extendMap_f`). This file records the
equivalent commutation squares and naturality compatibilities:

* `HomologicalComplex.extend_d_comp_extendXIso_hom`: the identifications intertwine the
  differentials of `K.extend e` and of `K`.
* `HomologicalComplex.extendMap_f_comp_extendXIso_hom`: the identifications intertwine
  `extendMap φ e` and `φ`.
* `ComplexShape.Embedding.extendSingleIso_hom_naturality` and
  `ComplexShape.Embedding.extendSingleIso_inv_naturality`: naturality of Mathlib's
  `HomologicalComplex.extendSingleIso` in the object argument.

## References

* Mathlib's `Mathlib/Algebra/Homology/Embedding/Extend.lean`.
* `TauCeti/Algebra/Homology/Embedding/Extend/Map.lean` for `HomologicalComplex.mapExtendIso` and
  `ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`.
* `TauCeti/Algebra/Homology/Embedding/Restriction/Basic.lean`, the counterpart for
  `e.restrictionFunctor`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v₁ u₁

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroObject C] [HasZeroMorphisms C] (e : c.Embedding c')

/-- In degrees in the image of `e.f`, the identifications of `K.extend e` with `K` intertwine
the differentials. -/
@[reassoc, elementwise]
theorem extend_d_comp_extendXIso_hom (K : HomologicalComplex C c) {i' j' : ι'} {i j : ι}
    (hi : e.f i = i') (hj : e.f j = j') :
    (K.extend e).d i' j' ≫ (K.extendXIso e hj).hom = (K.extendXIso e hi).hom ≫ K.d i j := by
  rw [extend_d_eq K e hi hj, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In a degree in the image of `e.f`, the identifications of the extended complexes with the
original ones intertwine the extension `extendMap φ e` of a chain map with `φ`. -/
@[reassoc, elementwise]
theorem extendMap_f_comp_extendXIso_hom {K L : HomologicalComplex C c} (φ : K ⟶ L) {i' : ι'}
    {i : ι} (h : e.f i = i') :
    (extendMap φ e).f i' ≫ (L.extendXIso e h).hom = (K.extendXIso e h).hom ≫ φ.f i := by
  rw [extendMap_f φ e h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HomologicalComplex

namespace ComplexShape.Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

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
