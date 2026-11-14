/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Ext
public import TauCeti.CategoryTheory.Linear.Yoneda
import TauCeti.CategoryTheory.Abelian.LeftDerived

/-!
# `Ext` in degree zero

In a `k`-linear abelian category with enough projectives, Mathlib's `Ext k C n` is the `n`-th left
derived functor of `Hom(-, Y)`, read in the opposite category of `k`-modules. In degree zero it
is `Hom(-, Y)` itself: `Hom(-, Y)` sends finite colimits to finite limits
(`CategoryTheory.preservesLimits_linearYoneda_obj`), so it is right exact as a functor to the
opposite category, and the zeroth left derived functor of a right exact functor is the functor
itself (`CategoryTheory.Functor.leftDerivedZeroIsoSelf`).

## Main declarations

* `CategoryTheory.extZeroIso`: the isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)`, whose inverse is the
  canonical comparison `CategoryTheory.Functor.fromLeftDerivedZero`
  (`CategoryTheory.extZeroIso_inv`).
* `CategoryTheory.extZeroIso_hom_naturality_left` and
  `CategoryTheory.extZeroIso_hom_naturality_right`: it is natural in both variables.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {k : Type w} [Ring k] [Linear k C]

/-- The isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)` for the left derived functor `Ext k C 0` of
`Hom(-, Y)`: the zeroth left derived functor of the right exact functor `Hom(-, Y)`, read in the
opposite category of `k`-modules, is `Hom(-, Y)` itself. -/
noncomputable def extZeroIso (X Y : C) :
    ((Ext k C 0).obj (op X)).obj Y ≅ ModuleCat.of k (X ⟶ Y) :=
  (((linearYoneda k C).obj Y).rightOp.leftDerivedZeroIsoSelf.app X).unop.symm

/-- The inverse of `Ext⁰(X, Y) ≅ Hom(X, Y)` is the canonical comparison from the zeroth left
derived functor of `Hom(-, Y)`, read in the opposite category of `k`-modules. -/
theorem extZeroIso_inv (X Y : C) :
    (extZeroIso (k := k) X Y).inv =
      (((linearYoneda k C).obj Y).rightOp.fromLeftDerivedZero.app X).unop :=
  (rfl)

/-- The isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)` is natural in `X`: precomposition with `f : X' ⟶ X`
on `Hom(-, Y)` corresponds to the action of `Ext k C 0` on `f`. -/
@[reassoc]
theorem extZeroIso_hom_naturality_left {X X' : C} (f : X' ⟶ X) (Y : C) :
    ((Ext k C 0).map f.op).app Y ≫ (extZeroIso X' Y).hom =
      (extZeroIso X Y).hom ≫ ((linearYoneda k C).obj Y).map f.op :=
  -- `Ext k C 0` is by definition `Hom(-, Y)` derived in the opposite category of `k`-modules, and
  -- Mathlib's `Ext` has no `simps` lemmas; the statement is the naturality square at `f` of the
  -- comparison `L₀ Hom(-, Y) ≅ Hom(-, Y)`, read in the opposite category. The two sides are typed
  -- in `ModuleCat.of k (X ⟶ Y)` and in `((linearYoneda k C).obj Y).obj (op X)`, which agree only
  -- after unfolding, so the square is transported with `Quiver.Hom.op_inj` rather than by
  -- rewriting.
  Quiver.Hom.op_inj
    (((linearYoneda k C).obj Y).rightOp.leftDerivedZeroIsoSelf.inv.naturality f).symm

/-- The isomorphism `Ext⁰(X, Y) ≅ Hom(X, Y)` is natural in `Y`: postcomposition with `g : Y ⟶ Y'`
on `Hom(X, -)` corresponds to the action of `Ext k C 0` on `g`. -/
@[reassoc]
theorem extZeroIso_hom_naturality_right (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((Ext k C 0).obj (op X)).map g ≫ (extZeroIso X Y').hom =
      (extZeroIso X Y).hom ≫ ((linearCoyoneda k C).obj (op X)).map g := by
  -- `Ext k C 0` acts on `g` by the natural transformation of left derived functors induced by
  -- `(linearYoneda k C).map g`, and `((linearCoyoneda k C).obj (op X)).map g` is the component of
  -- `(linearYoneda k C).map g` at `X`; Mathlib's `Ext` has no `simps` lemmas. `h` is therefore the
  -- `unop` of the naturality of `fromLeftDerivedZero` in the functor at `X`, with
  -- `extZeroIso_inv` and `unop_comp` holding by definition. The two sides are typed in
  -- `ModuleCat.of k (X ⟶ Y)` and in `((linearCoyoneda k C).obj (op X)).obj Y`, which agree only
  -- after unfolding, so `extZeroIso` is cancelled with `Iso.inv_comp_eq` and `Iso.eq_comp_inv`
  -- rather than by rewriting.
  have h : (extZeroIso X Y).inv ≫ ((Ext k C 0).obj (op X)).map g =
      ((linearCoyoneda k C).obj (op X)).map g ≫ (extZeroIso X Y').inv :=
    congrArg Quiver.Hom.unop (NatTrans.congr_app
      (NatTrans.leftDerived_zero_comp_fromLeftDerivedZero ((linearYoneda k C).map g).rightOp) X)
  exact (Iso.eq_comp_inv _).mp (((Iso.inv_comp_eq _).mp h).trans (Category.assoc _ _ _).symm)

end CategoryTheory
