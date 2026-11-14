/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Action
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

/-!
# Limits and faithfulness of actions viewed as functors

A multiplicative action of a monoid `G` on a type `X` is a functor
`CategoryTheory.actionAsFunctor G X : SingleObj G ⥤ Type u`, sending the unique object to `X`
and `g : G` to the map `x ↦ g • x`.

## Main definitions

* `CategoryTheory.actionAsFunctor.limitEquivFixedPoints`: the limit of this functor is the
  fixed-point set `MulAction.fixedPoints G X`.

## Main results

* `CategoryTheory.actionAsFunctor_map_apply`: the functor sends `g` to the action of `g`.
* `CategoryTheory.actionAsFunctor.coe_limitEquivFixedPoints`,
  `CategoryTheory.actionAsFunctor.limit_π_limitEquivFixedPoints_symm`: the equivalence is the
  projection to the unique object, and its inverse sends a fixed point to the family constant at
  it.
* `CategoryTheory.actionAsFunctor.faithful_iff_faithfulSMul`: the functor is faithful exactly
  when the action is faithful.

The equivalence specializes Mathlib's `CategoryTheory.Limits.SingleObj.Types.limitEquivFixedPoints`,
stated for the action that an arbitrary functor `SingleObj G ⥤ Type u` induces on its unique value.

## Attribution

Adapted from `Mei/CategoryTheory/ActionAsFunctor/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained; the file uses the requested Tau Ceti copyright header.
-/

public section

universe u v

namespace CategoryTheory

open Limits

variable (G : Type v) [Monoid G] (X : Type u) [MulAction G X]

/-- The functor `actionAsFunctor G X` sends `g : G` to the action of `g`. -/
-- A pre-lemma: `CategoryTheory.actionAsFunctor_map` would otherwise first rewrite the map to
-- `TypeCat.ofHom`, whose application `TypeCat.ofHom_apply` cannot then rewrite, because
-- `(actionAsFunctor G X).obj a` is `X` only up to unfolding `actionAsFunctor`.
@[simp↓]
theorem actionAsFunctor_map_apply {a b : SingleObj G} (g : a ⟶ b) (x : X) :
    (actionAsFunctor G X).map g x = (g : G) • x := by
  rw [actionAsFunctor_map]
  exact TypeCat.ofHom_apply _ _

namespace actionAsFunctor

/-- The limit of a multiplicative action of `G` on `X`, viewed as a functor on `SingleObj G`, is
the fixed-point set of the action. -/
noncomputable def limitEquivFixedPoints :
    limit (actionAsFunctor G X) ≃ MulAction.fixedPoints G X :=
  (SingleObj.Types.limitEquivFixedPoints _).trans <| Equiv.subtypeEquivRight fun x =>
    -- The action induced on `(actionAsFunctor G X).obj (SingleObj.star G)` is, by definition,
    -- `g • x = (actionAsFunctor G X).map g x`.
    forall_congr' fun g => by rw [← actionAsFunctor_map_apply G X g x]; exact Iff.rfl

/-- The equivalence `CategoryTheory.actionAsFunctor.limitEquivFixedPoints` is the projection to
the unique object of `SingleObj G`. -/
@[simp]
theorem coe_limitEquivFixedPoints (s : limit (actionAsFunctor G X)) :
    (limitEquivFixedPoints G X s : X) = limit.π (actionAsFunctor G X) (SingleObj.star G) s := by
  rw [limitEquivFixedPoints]
  -- `erw` unfolds `(actionAsFunctor G X).obj _` to `X` across the subtype equivalence.
  erw [Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
  exact SingleObj.Types.limitEquivFixedPoints_apply_coe _ s

/-- The inverse of `CategoryTheory.actionAsFunctor.limitEquivFixedPoints` sends a fixed point to
the family constant at it. -/
@[simp]
theorem limit_π_limitEquivFixedPoints_symm (x : MulAction.fixedPoints G X) (j : SingleObj G) :
    limit.π (actionAsFunctor G X) j ((limitEquivFixedPoints G X).symm x) = (x : X) := by
  rw [limitEquivFixedPoints]
  -- `erw` unfolds `(actionAsFunctor G X).obj _` to `X` across the subtype equivalence.
  erw [Equiv.symm_trans_apply]
  simp only [SingleObj.Types.limitEquivFixedPoints_symm_apply, Types.limitEquivSections_symm_apply,
    SingleObj.Types.sections.equivFixedPoints_symm_apply_coe]
  exact Equiv.subtypeEquivRight_symm_apply_coe _ x

/-- A multiplicative action, viewed as a functor on `SingleObj G`, is faithful exactly when the
action is faithful. -/
theorem faithful_iff_faithfulSMul : (actionAsFunctor G X).Faithful ↔ FaithfulSMul G X := by
  refine ⟨fun _ => ⟨fun {g g'} hgg' => ?_⟩, fun _ => ⟨fun {_ _} g g' hgg' => ?_⟩⟩
  · refine (actionAsFunctor G X).map_injective (X := SingleObj.star G) (Y := SingleObj.star G) ?_
    ext x
    exact (actionAsFunctor_map_apply G X g x).trans
      ((hgg' x).trans (actionAsFunctor_map_apply G X g' x).symm)
  · refine FaithfulSMul.eq_of_smul_eq_smul (α := X) fun x => ?_
    exact (actionAsFunctor_map_apply G X g x).symm.trans
      ((congrArg (fun f => f x) hgg').trans (actionAsFunctor_map_apply G X g' x))

/-- A faithful multiplicative action yields a faithful action viewed as a functor on
one-object categories. -/
instance instFaithful_of_faithfulSMul [FaithfulSMul G X] : (actionAsFunctor G X).Faithful :=
  (faithful_iff_faithfulSMul G X).mpr inferInstance

end actionAsFunctor

end CategoryTheory
