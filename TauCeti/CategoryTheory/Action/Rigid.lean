/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Drinfeld
public import TauCeti.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Duals of actions on underlying objects

For a right rigid monoidal category `V` and a group `H`, Mathlib makes `Action V H` right rigid by
pulling the right duals of the functor category `SingleObj H ⥤ V` back along the equivalence
`Action.functorCategoryEquivalence`. The underlying object of the dual action is the dual of the
underlying object (`Action.rightDual_v`). This file records that the same holds for the structure
maps: the evaluation and coevaluation of the pairing `(X, Xᘁ)` in `Action V H` have, as underlying
morphisms of `V`, the evaluation and coevaluation of `(X.V, X.Vᘁ)`.

These are the identities needed to compute categorical constructions built from duals in
`Action V H` on underlying objects. The first such construction is the Drinfeld isomorphism
`X ≅ Xᘁᘁ` of a braided category: when `V` is braided, so is `Action V H`, and the Drinfeld
isomorphism of an action is that of its underlying object.

## Main results

* `Action.evaluation_hom`: the underlying morphism of `ε_ X Xᘁ` is `ε_ X.V X.Vᘁ`;
* `Action.coevaluation_hom`: the underlying morphism of `η_ X Xᘁ` is `η_ X.V X.Vᘁ`;
* `Action.drinfeldIso_hom_hom`, `Action.drinfeldIso_inv_hom`: the Drinfeld isomorphism of an
  action is that of its underlying object.
-/

public section

open CategoryTheory MonoidalCategory TauCeti Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] [RightRigidCategory V]
  {H : Type*} [Group H]

omit [MonoidalCategory V] [RightRigidCategory V] in
/-- The inverse of the counit along which `Action V H` inherits its right duals has identity
components: its forward component is the identity by definition, so its inverse is too. -/
private theorem toEquivalence_counitIso_inv_app_app (F : SingleObj H ⥤ V) (x : SingleObj H) :
    ((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app F).inv.app x =
      𝟙 _ :=
  Iso.inv_ext (f := ((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app
    F).app x) (Category.comp_id _)

/-- The evaluation of a dual action is the evaluation of the dual of the underlying object. -/
@[simp]
theorem evaluation_hom (X : Action V H) : (ε_ X Xᘁ).hom = ε_ X.V X.Vᘁ := by
  -- Take the component of `map_evaluation_hasRightDualOfEquivalence` at the single object. The
  -- structure maps of the equivalence and the components of its counit are identities by
  -- definition, which is how this statement of `h` is accepted.
  have h : (ε_ X Xᘁ).hom = 𝟙 _ ≫ (𝟙 X.Vᘁ ▷ X.V ≫ ε_ X.V X.Vᘁ) ≫ 𝟙 _ :=
    congrArg (NatTrans.app · (SingleObj.star H)) (map_evaluation_hasRightDualOfEquivalence
      (functorCategoryEquivalence V H).toAdjunction X)
  simpa using h

/-- The coevaluation of a dual action is the coevaluation of the dual of the underlying
object. -/
@[simp]
theorem coevaluation_hom (X : Action V H) : (η_ X Xᘁ).hom = η_ X.V X.Vᘁ := by
  -- As for `Action.evaluation_hom`, except that the inverse of the counit is an identity only
  -- propositionally, by `toEquivalence_counitIso_inv_app_app`. Its component and whiskering are
  -- stated between the objects `X.Vᘁ` and `X.V ⊗ X.Vᘁ`, so that `whiskerLeft_id` and
  -- `Category.comp_id` apply.
  have hc : (((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app
      ((functorCategoryEquivalence V H).functor.obj X)ᘁ).inv.app (SingleObj.star H) :
        X.Vᘁ ⟶ X.Vᘁ) = 𝟙 X.Vᘁ :=
    toEquivalence_counitIso_inv_app_app _ _
  have h : (η_ X Xᘁ).hom = 𝟙 _ ≫ (η_ X.V X.Vᘁ ≫ whiskerLeft (Y₁ := X.Vᘁ) (Y₂ := X.Vᘁ) X.V
      (((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app
        ((functorCategoryEquivalence V H).functor.obj X)ᘁ).inv.app (SingleObj.star H))) ≫ 𝟙 _ :=
    congrArg (NatTrans.app · (SingleObj.star H)) (map_coevaluation_hasRightDualOfEquivalence
      (functorCategoryEquivalence V H).toAdjunction X)
  rw [hc] at h
  simpa using h

variable [BraidedCategory V]

/-- The Drinfeld isomorphism `X ≅ Xᘁᘁ` of an action is, on underlying objects, the Drinfeld
isomorphism of the underlying object. -/
@[simp]
theorem drinfeldIso_hom_hom (X : Action V H) :
    (drinfeldIso X).hom.hom = (drinfeldIso X.V).hom := by
  rw [drinfeldIso_hom_eq, drinfeldIso_hom_eq]
  simp only [comp_hom, rightUnitor_inv_hom, whiskerLeft_hom, coevaluation_hom,
    associator_inv_hom, whiskerRight_hom, evaluation_hom, leftUnitor_hom_hom]
  -- The remaining difference is only in how the double dual `Xᘁᘁ.V = X.Vᘁᘁ` is presented.
  rfl

/-- The inverse of the Drinfeld isomorphism of an action is, on underlying objects, the inverse
of the Drinfeld isomorphism of the underlying object. -/
@[simp]
theorem drinfeldIso_inv_hom (X : Action V H) :
    (drinfeldIso X).inv.hom = (drinfeldIso X.V).inv := by
  have h := congrArg Hom.hom (drinfeldIso X).hom_inv_id
  rw [comp_hom, drinfeldIso_hom_hom, id_hom] at h
  exact Iso.inv_ext' h

end Action
