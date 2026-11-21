/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Naturality of extension of single complexes along complex-shape embeddings

Let `e : c.Embedding c'` be an embedding of complex shapes. This file records naturality
compatibilities for Mathlib's `HomologicalComplex.extendSingleIso`:

* `ComplexShape.Embedding.extendSingleIso_hom_naturality` and
  `ComplexShape.Embedding.extendSingleIso_inv_naturality`: naturality of Mathlib's
  `HomologicalComplex.extendSingleIso` in the object argument.

## References

* Mathlib's `Mathlib/Algebra/Homology/Embedding/Extend.lean`.
* `TauCeti/Algebra/Homology/Embedding/MapExtend.lean` for `HomologicalComplex.mapExtendIso` and
  `ComplexShape.Embedding.extendFunctorCompMapHomologicalComplexIso`.
* `TauCeti/Algebra/Homology/Embedding/Restriction/Basic.lean`, the counterpart for
  `e.restrictionFunctor`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v₁ u₁

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

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
