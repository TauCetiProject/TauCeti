/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Linear equivalence between shifted single-object derived morphisms and `Ext`

Mathlib's `CategoryTheory.Abelian.Ext.homLinearEquiv` identifies `Abelian.Ext X Y n` with shifted
morphisms from `(singleFunctor C 0).obj X` to `((singleFunctor C 0).obj Y)⟦n⟧`. In applications
such as Hom finiteness (`TauCeti.Algebra.Homology.DerivedCategory.FiniteHom`), objects naturally
appear placed in arbitrary degrees `a, b : ℤ` via `singleFunctor C a` and `singleFunctor C b`.

This file provides the `R`-linear equivalence
`TauCeti.DerivedCategory.singleFunctorHomLinearEquivExt` identifying
`((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y)` with `Abelian.Ext X Y n` whenever
`a - b = n`, together with `@[simp]` characterizations of its forward and inverse maps.
-/

public section

open CategoryTheory _root_.DerivedCategory

universe t w' w v u

namespace TauCeti.DerivedCategory

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w'} C] [HasDerivedCategory.{w} C]

/-- Morphisms `(singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y` in the derived category
are `R`-linearly equivalent to `Abelian.Ext X Y n` whenever `a - b = n`. -/
noncomputable def singleFunctorHomLinearEquivExt (X Y : C) (a b : ℤ) (n : ℕ) (h : a - b = n) :
    ((singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) ≃ₗ[R] Abelian.Ext.{w'} X Y n :=
  let eX : ((singleFunctor C a).obj X)⟦a⟧ ≅ (singleFunctor C 0).obj X :=
    ((singleFunctors C).shiftIso a 0 a (add_zero a)).app X
  let eY : ((singleFunctor C b).obj Y)⟦a⟧ ≅ ((singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ :=
    (shiftFunctor (_root_.DerivedCategory C) a).mapIso
      (((singleFunctors C).shiftIso (-b) b 0 (by omega)).symm.app Y) ≪≫
    (shiftFunctorAdd' (_root_.DerivedCategory C) (-b) a (n : ℤ) (by omega)).symm.app
      ((singleFunctor C 0).obj Y)
  ((shiftFunctor (_root_.DerivedCategory C) a).homLinearEquiv R _ _).trans <|
    (Linear.homCongr R eX eY).trans Abelian.Ext.homLinearEquiv.symm

/-- The image of a morphism under `singleFunctorHomLinearEquivExt` is given by shifting by `a` and
conjugating by the canonical shift isomorphisms for `singleFunctors`. -/
@[simp]
theorem singleFunctorHomLinearEquivExt_apply_hom (X Y : C) (a b : ℤ) (n : ℕ) (h : a - b = n)
    (f : (singleFunctor C a).obj X ⟶ (singleFunctor C b).obj Y) :
    (singleFunctorHomLinearEquivExt R X Y a b n h f).hom =
      ((singleFunctors C).shiftIso a 0 a (add_zero a)).inv.app X ≫ f⟦a⟧' ≫
        (((singleFunctors C).shiftIso (-b) b 0 (by omega)).inv.app Y)⟦a⟧' ≫
        (shiftFunctorAdd' (_root_.DerivedCategory C) (-b) a (n : ℤ) (by omega)).inv.app
          ((singleFunctor C 0).obj Y) := by
  rw [← Abelian.Ext.homAddEquiv_apply, ← AddEquiv.toFun_eq_coe,
    ← Abelian.Ext.homLinearEquiv_apply (R := R)]
  simp [singleFunctorHomLinearEquivExt, Linear.homCongr_apply, Category.assoc]

/-- The inverse of `singleFunctorHomLinearEquivExt` conjugates `x.hom` back along the canonical
shift isomorphisms for `singleFunctors` and takes the preimage under shifting by `a`. -/
@[simp]
theorem singleFunctorHomLinearEquivExt_symm_apply (X Y : C) (a b : ℤ) (n : ℕ) (h : a - b = n)
    (x : Abelian.Ext.{w'} X Y n) :
    (singleFunctorHomLinearEquivExt R X Y a b n h).symm x =
      (shiftFunctor (_root_.DerivedCategory C) a).preimage
        (((singleFunctors C).shiftIso a 0 a (add_zero a)).hom.app X ≫ x.hom ≫
          (shiftFunctorAdd' (_root_.DerivedCategory C) (-b) a (n : ℤ) (by omega)).hom.app
            ((singleFunctor C 0).obj Y) ≫
          (((singleFunctors C).shiftIso (-b) b 0 (by omega)).hom.app Y)⟦a⟧') := by
  simp [singleFunctorHomLinearEquivExt, Linear.homCongr_symm_apply]

end TauCeti.DerivedCategory
