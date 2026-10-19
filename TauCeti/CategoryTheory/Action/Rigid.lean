/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Drinfeld

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

open CategoryTheory MonoidalCategory TauCeti

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] [RightRigidCategory V]
  {H : Type*} [Group H]

/-- The evaluation of a dual action is the evaluation of the dual of the underlying object. -/
@[simp]
theorem evaluation_hom (X : Action V H) : (ε_ X Xᘁ).hom = ε_ X.V X.Vᘁ := by
  -- Mathlib defines `ε_ X Xᘁ` as a preimage under the equivalence with the functor category, so
  -- we read off the underlying morphism as the component of its image there.
  change ((functorCategoryEquivalence V H).functor.map (ε_ X Xᘁ)).app (SingleObj.star H) = _
  -- The structure maps of the equivalence are identities, and the right dual of the functor
  -- category is transported across the counit, whose component is an identity.
  erw [Functor.map_preimage, NatTrans.comp_app, NatTrans.comp_app, Category.id_comp,
    Category.comp_id, TauCeti.exactPairingCongrRight_evaluation, NatTrans.comp_app,
    Monoidal.FunctorCategory.whiskerRight_app, id_whiskerRight, Category.id_comp]
  rfl

/-- The coevaluation of a dual action is the coevaluation of the dual of the underlying
object. -/
@[simp]
theorem coevaluation_hom (X : Action V H) : (η_ X Xᘁ).hom = η_ X.V X.Vᘁ := by
  -- As for `Action.evaluation_hom`, read off the component of the image in the functor category.
  change ((functorCategoryEquivalence V H).functor.map (η_ X Xᘁ)).app (SingleObj.star H) = _
  erw [Functor.map_preimage, NatTrans.comp_app, NatTrans.comp_app, Category.id_comp,
    Category.comp_id, TauCeti.exactPairingCongrRight_coevaluation, NatTrans.comp_app,
    Monoidal.FunctorCategory.whiskerLeft_app]
  -- The inverse of the counit component of the equivalence is the identity.
  dsimp [Adjunction.toEquivalence, Equivalence.toAdjunction]
  erw [asIso_inv, NatIso.isIso_inv_app]
  dsimp [functorCategoryEquivalence, FunctorCategoryEquivalence.counitIso]
  erw [IsIso.inv_id, MonoidalCategory.whiskerLeft_id, Category.comp_id]
  rfl

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
