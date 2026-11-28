/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Nerves of categories of families

A string of arrows between families is a family of strings of arrows. Thus the nerve of
the category of `I`-indexed families in `C` is the product of copies of `nerve C`, with
projections induced by coordinate evaluation. This includes the empty family.

The index type is in `Type`, so the comparison preserves the natural universe `max u v`
of the nerve without imposing a relation between the object and morphism universes of `C`.
-/

public section

universe v u

open CategoryTheory Limits Simplicial

namespace CategoryTheory.nerve

variable (C : Type u) [Category.{v} C] (I : Type)

/-- A string of arrows between families is a family of strings of arrows. -/
def piSimplexEquiv (n : SimplexCategoryᵒᵖ) :
    (nerve (I → C)).obj n ≃ (I → (nerve C).obj n) where
  toFun s i := s ⋙ CategoryTheory.Pi.eval (fun _ : I ↦ C) i
  invFun s := Functor.pi' s
  left_inv _ := CategoryTheory.Functor.hext (fun _ ↦ rfl) (fun _ _ _ ↦ HEq.rfl)
  right_inv s := funext fun i ↦ Functor.pi'_eval s i

/-- The coordinate string is obtained by postcomposition with coordinate evaluation. -/
@[simp]
lemma piSimplexEquiv_apply (n : SimplexCategoryᵒᵖ) (s : (nerve (I → C)).obj n) (i : I) :
    piSimplexEquiv C I n s i = s ⋙ CategoryTheory.Pi.eval (fun _ : I ↦ C) i :=
  (rfl)

/-- The inverse assembles a family of strings by Mathlib's pointwise functor constructor. -/
lemma piSimplexEquiv_symm_apply (n : SimplexCategoryᵒᵖ) (s : I → (nerve C).obj n) :
    (piSimplexEquiv C I n).symm s = Functor.pi' s :=
  (rfl)

/-- Coordinate evaluation on strings gives the comparison to the product of nerves. -/
noncomputable def piComparison : nerve (I → C) ⟶ ∏ᶜ (fun _ : I ↦ nerve C) :=
  Pi.lift fun i ↦ nerveMap (CategoryTheory.Pi.eval (fun _ : I ↦ C) i)

/-- The projections of the comparison are the nerves of coordinate evaluation. -/
@[reassoc (attr := simp)]
lemma piComparison_π (i : I) :
    piComparison C I ≫ Pi.π (fun _ : I ↦ nerve C) i =
      nerveMap (CategoryTheory.Pi.eval (fun _ : I ↦ C) i) :=
  Pi.lift_comp_π _ _

/-- The comparison on simplices is the equivalence between strings of families and
families of strings, after the canonical identifications of categorical products. -/
lemma piComparison_app (n : SimplexCategoryᵒᵖ) (s : (nerve (I → C)).obj n) :
    (Types.productIso (fun _ : I ↦ (nerve C).obj n)).hom
      ((piObjIso (fun _ : I ↦ nerve C) n).hom ((piComparison C I).app n s)) =
        piSimplexEquiv C I n s := by
  funext i
  rw [Types.productIso_hom_comp_eval_apply]
  rw [← ConcreteCategory.comp_apply, piObjIso_hom_comp_π]
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, piComparison_π]
  rfl

/-- The nerve of a category of families is the product of the nerves. -/
instance isIso_piComparison : IsIso (piComparison C I) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  let e := piObjIso (fun _ : I ↦ nerve C) n ≪≫
    Types.productIso (fun _ : I ↦ (nerve C).obj n)
  have h : Function.Bijective (fun s ↦ e.hom ((piComparison C I).app n s)) := by
    simpa only [e, Iso.trans_hom, ConcreteCategory.comp_apply, piComparison_app] using
      (piSimplexEquiv C I n).bijective
  exact (isIso_iff_bijective _).2
    (Function.Bijective.of_comp_left h ((isIso_iff_bijective e.hom).1 inferInstance).1)

end CategoryTheory.nerve
