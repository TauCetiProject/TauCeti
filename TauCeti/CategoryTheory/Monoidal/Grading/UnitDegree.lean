/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Grading.Universal.Basic
public import TauCeti.CategoryTheory.Semisimple.UnitSummands.Basic

/-!
# Universal grading degrees of unit summands

Every simple summand of the tensor unit `𝟙_ C` in a finite semisimple monoidal category is
tensor-idempotent (`UnitSimpleClasses.tensorSelfIso`), and therefore has trivial degree in
`TauCeti.universalGradingGroup C`.

## Main declarations

* `TauCeti.universalGradingGroup.degree_unitSummand`: every simple summand `I : UnitSimpleClasses C`
  has `degree I.val = 1`.
* `TauCeti.universalGradingGroup.degree_classOf_eq_one_of_hom_to_unit_ne_zero`: any simple object
  admitting a nonzero morphism to `𝟙_ C` has trivial universal degree.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti.universalGradingGroup

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [IsFiniteSemisimpleCategory C]

/-- Every simple summand of the tensor unit has trivial degree in `universalGradingGroup C`. -/
@[simp] theorem degree_unitSummand (I : UnitSimpleClasses C) :
    universalGradingGroup.degree I.val = 1 := by
  let a := (UnitSimpleClasses.tensorSelfIso I).symm
  have ha : a.hom ≠ 0 := fun h ↦
    CategoryTheory.id_ne_zero I.repr (by rw [← a.hom_inv_id, h, zero_comp])
  simpa only [SimpleClasses.classOf_repr] using degree_classOf_eq_one_of_hom_tensor_self_ne_zero ha

/-- Any simple object mapping nontrivially into `𝟙_ C` has trivial degree in
`universalGradingGroup C`. -/
theorem degree_classOf_eq_one_of_hom_to_unit_ne_zero {X : C} [Simple X] {f : X ⟶ 𝟙_ C}
    (hf : f ≠ 0) : universalGradingGroup.degree (SimpleClasses.classOf X) = 1 := by
  simpa only [UnitSimpleClasses.val_mkOfHomNeZero] using
    universalGradingGroup.degree_unitSummand (UnitSimpleClasses.mkOfHomNeZero hf)

end TauCeti.universalGradingGroup
