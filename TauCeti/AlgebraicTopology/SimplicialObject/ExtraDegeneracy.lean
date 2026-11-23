/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Naturality of extra degeneracies on constant simplicial objects

This file supplements `Mathlib.AlgebraicTopology.ExtraDegeneracy` with naturality of the inverse
homotopy equivalence `(ExtraDegeneracy.const X).homotopyEquiv.inv` for constant augmented
simplicial objects.
-/

public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

/-- The forward map of `(ExtraDegeneracy.const X).homotopyEquiv` is the canonical augmentation
`AlternatingFaceMapComplex.ε.app (SimplicialObject.Augmented.const.obj X)`. -/
@[simp]
lemma const_homotopyEquiv_hom {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (X : C) :
    (const X).homotopyEquiv.hom =
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj X) :=
  rfl

/-- The backward map of `(ExtraDegeneracy.const X).homotopyEquiv` is the canonical section
`(ChainComplex.fromSingle₀Equiv _ X).symm (𝟙 X)`. -/
@[simp]
lemma const_homotopyEquiv_inv {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (X : C) :
    (const X).homotopyEquiv.inv =
      (ChainComplex.fromSingle₀Equiv
          ((AlgebraicTopology.alternatingFaceMapComplex C).obj
            ((SimplicialObject.const C).obj X)) X).symm (𝟙 X) :=
  rfl

/-- Degree-zero component of `const_homotopyEquiv_inv_naturality`. The `erw` steps are needed
because `(const X).homotopyEquiv.inv` is typed over
`(ChainComplex.single₀ C).obj (Augmented.point.obj (Augmented.const.obj X))` and
`AlternatingFaceMapComplex.obj (Augmented.drop.obj (Augmented.const.obj X))`, which match
`(ChainComplex.single₀ C).obj X` and
`(alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj X)` only up to unfolding
`Augmented.point`, `Augmented.drop`, `Augmented.const`, and `AlternatingFaceMapComplex.obj`. -/
private lemma const_homotopyEquiv_inv_naturality_f_zero {C : Type u} [Category.{v} C]
    [Preadditive C] [HasZeroObject C] {X Y : C} (f : X ⟶ Y) :
    ((ChainComplex.single₀ C).map f ≫ (const Y).homotopyEquiv.inv).f 0 =
      ((const X).homotopyEquiv.inv ≫
        (AlgebraicTopology.alternatingFaceMapComplex C).map
          ((SimplicialObject.const C).map f)).f 0 := by
  dsimp only [ExtraDegeneracy.homotopyEquiv]
  -- Unfold across `Augmented.const` / `AlternatingFaceMapComplex` / `fromSingle₀Equiv`.
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero,
    ChainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    ChainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    AlgebraicTopology.alternatingFaceMapComplex_map_f]
  dsimp
  erw [Category.comp_id, Category.id_comp]

/-- Naturality of the inverse homotopy equivalence `(ExtraDegeneracy.const X).homotopyEquiv.inv`
with respect to morphisms `f : X ⟶ Y`. -/
@[reassoc]
lemma const_homotopyEquiv_inv_naturality {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] {X Y : C} (f : X ⟶ Y) :
    (ChainComplex.single₀ C).map f ≫ (const Y).homotopyEquiv.inv =
      (const X).homotopyEquiv.inv ≫
        (AlgebraicTopology.alternatingFaceMapComplex C).map ((SimplicialObject.const C).map f) := by
  ext
  exact const_homotopyEquiv_inv_naturality_f_zero f

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy
