/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Rigid.Drinfeld
public import TauCeti.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Duals of actions on underlying objects

For a right rigid monoidal category `V` and a group `H`, Mathlib makes `Action V H` right rigid by
pulling the right duals of the functor category `SingleObj H ⥤ V` back along the equivalence
`Action.functorCategoryEquivalence`. The underlying object of the dual action is the dual of the
underlying object (`Action.rightDual_v`). This file records that the same holds for the structure
maps: the evaluation and coevaluation of the pairing `(X, Xᘁ)` in `Action V H` have, as underlying
morphisms of `V`, the evaluation and coevaluation of `(X.V, X.Vᘁ)`. The same holds for the left
duals of a left rigid `V` (`Action.leftDual_v`).

These are the identities needed to compute categorical constructions built from duals in
`Action V H` on underlying objects. The first such construction is the Drinfeld isomorphism
`X ≅ Xᘁᘁ` of a braided category: when `V` is braided, so is `Action V H`, and the Drinfeld
isomorphism of an action is that of its underlying object.

## Main results

* `Action.evaluation_hom`: the underlying morphism of `ε_ X Xᘁ` is `ε_ X.V X.Vᘁ`;
* `Action.coevaluation_hom`: the underlying morphism of `η_ X Xᘁ` is `η_ X.V X.Vᘁ`;
* `Action.leftEvaluation_hom`, `Action.leftCoevaluation_hom`: the same for the pairing
  `(ᘁX, X)`;
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
  -- As for `Action.evaluation_hom`, take the component at the single object. The counit's
  -- forward component is the identity by definition, so uniqueness of inverses identifies its
  -- inverse with the identity too. The stated types let the identity whiskering simplify in `V`.
  let e : X.Vᘁ ≅ X.Vᘁ :=
    ((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app
      ((functorCategoryEquivalence V H).functor.obj X)ᘁ).app (SingleObj.star H)
  have hc : e.inv = 𝟙 X.Vᘁ := Iso.inv_ext (f := e) (Category.comp_id _)
  have h : (η_ X Xᘁ).hom = 𝟙 _ ≫ (η_ X.V X.Vᘁ ≫ X.V ◁ e.inv) ≫ 𝟙 _ :=
    congrArg (NatTrans.app · (SingleObj.star H)) (map_coevaluation_hasRightDualOfEquivalence
      (functorCategoryEquivalence V H).toAdjunction X)
  simpa only [hc, whiskerLeft_id, Category.id_comp, Category.comp_id] using h

variable [BraidedCategory V]

/-- The Drinfeld isomorphism `X ≅ Xᘁᘁ` of an action is, on underlying objects, the Drinfeld
isomorphism of the underlying object. -/
@[simp]
theorem drinfeldIso_hom_hom (X : Action V H) :
    (drinfeldIso X).hom.hom = (drinfeldIso X.V).hom := by
  -- The pairing is in V; h matches by Action.rightDual_v, which is rfl also for the double dual.
  apply ExactPairing.rightHom_ext (X := X.Vᘁ) (Y := (X.Vᘁ : V)ᘁ)
  have h := congrArg Hom.hom (drinfeldIso_hom_comp_evaluation X)
  simp only [comp_hom, whiskerRight_hom, evaluation_hom, β_hom_hom] at h
  exact h.trans (drinfeldIso_hom_comp_evaluation X.V).symm

/-- The inverse of the Drinfeld isomorphism of an action is, on underlying objects, the inverse
of the Drinfeld isomorphism of the underlying object. -/
@[simp]
theorem drinfeldIso_inv_hom (X : Action V H) :
    (drinfeldIso X).inv.hom = (drinfeldIso X.V).inv := by
  have h := congrArg Hom.hom (drinfeldIso X).hom_inv_id
  rw [comp_hom, drinfeldIso_hom_hom, id_hom] at h
  exact Iso.inv_ext' h

end Action

namespace Action

variable {V : Type*} [Category* V] [MonoidalCategory V] [LeftRigidCategory V]
  {H : Type*} [Group H]

/-- The evaluation of a left dual action is the evaluation of the left dual of the underlying
object. -/
@[simp]
theorem leftEvaluation_hom (X : Action V H) : (ε_ (ᘁX) X).hom = ε_ (ᘁX.V) X.V := by
  -- As for `Action.evaluation_hom`, take the component at the single object of
  -- `map_evaluation_hasLeftDualOfEquivalence`; the structure maps of the equivalence and the
  -- components of its counit are identities by definition.
  have h : (ε_ (ᘁX) X).hom = 𝟙 _ ≫ (X.V ◁ 𝟙 (ᘁX.V) ≫ ε_ (ᘁX.V) X.V) ≫ 𝟙 _ :=
    congrArg (NatTrans.app · (SingleObj.star H)) (map_evaluation_hasLeftDualOfEquivalence
      (functorCategoryEquivalence V H).toAdjunction X)
  simpa using h

/-- The coevaluation of a left dual action is the coevaluation of the left dual of the
underlying object. -/
@[simp]
theorem leftCoevaluation_hom (X : Action V H) : (η_ (ᘁX) X).hom = η_ (ᘁX.V) X.V := by
  -- As for `Action.coevaluation_hom`, the inverse of the counit's component is the identity by
  -- uniqueness of inverses. The left dual is written `_` where the notation `ᘁ` would be
  -- ambiguous between objects and morphisms.
  let e : (ᘁX.V) ≅ (ᘁX.V) :=
    ((functorCategoryEquivalence V H).toAdjunction.toEquivalence.counitIso.app
      ᘁ((functorCategoryEquivalence V H).functor.obj X)).app (SingleObj.star H)
  have hc : e.inv = 𝟙 _ := Iso.inv_ext (f := e) (Category.comp_id _)
  have h : (η_ (ᘁX) X).hom = 𝟙 _ ≫ (η_ _ X.V ≫ e.inv ▷ X.V) ≫ 𝟙 _ :=
    congrArg (NatTrans.app · (SingleObj.star H)) (map_coevaluation_hasLeftDualOfEquivalence
      (functorCategoryEquivalence V H).toAdjunction X)
  simpa only [hc, id_whiskerRight, Category.id_comp, Category.comp_id] using h

end Action
