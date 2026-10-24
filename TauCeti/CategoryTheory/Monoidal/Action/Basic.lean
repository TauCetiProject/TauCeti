/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# Action functors of a monoidal left action

For a left action of a monoidal category `C` on a category `D`, this file records how the
action functors `actionLeft D c : D ⥤ D` compose and invert.

* `actionLeftTensorIso` identifies the action functor of `c ⊗ c'` with the composite
  `actionLeft D c' ⋙ actionLeft D c`, with components the associator `αₗ c c'`. In particular
  a left action of a monoid `M` (that is, of `Discrete M`) satisfies `T (h * g) ≅ T g ⋙ T h`.
* `actionLeftEquivOfIso` shows that the action functor of an object with a tensor inverse is an
  equivalence; `actionLeftEquivalence` specializes this to `Discrete G` for a group `G`, where
  the inverse of the action functor of `g` is the action functor of `g⁻¹`.
* `actionHomLeft_eq_eqToHom`: when `C` is discrete, the action of a morphism of `C` is an
  `eqToHom`.
-/

public section

namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction

variable {C : Type*} [Category* C] [MonoidalCategory C] (D : Type*) [Category* D]
  [MonoidalLeftAction C D]

/-- The action functor of a tensor product is the composite of the action functors, in the
order `c ⊗ c' ↦ actionLeft D c' ⋙ actionLeft D c`; its components are `αₗ c c' d`. -/
def actionLeftTensorIso (c c' : C) :
    actionLeft D (c ⊗ c') ≅ actionLeft D c' ⋙ actionLeft D c :=
  ((actionAssocNatIso C D).app c).app c'

-- The construction bodies in this file are not exposed, so their projection lemmas are proved
-- with `by rfl`: a term-mode `rfl` proof would be checked as an exported definitional lemma.
@[simp]
lemma actionLeftTensorIso_hom_app (c c' : C) (d : D) :
    (actionLeftTensorIso D c c').hom.app d = (αₗ c c' d).hom := by
  rfl

@[simp]
lemma actionLeftTensorIso_inv_app (c c' : C) (d : D) :
    (actionLeftTensorIso D c c').inv.app d = (αₗ c c' d).inv := by
  rfl

/-- If `c' ⊗ c ≅ 𝟙_ C` and `c ⊗ c' ≅ 𝟙_ C`, then the action functor of `c` is an equivalence
whose inverse is the action functor of `c'`. -/
def actionLeftEquivOfIso {c c' : C} (e : c' ⊗ c ≅ 𝟙_ C) (e' : c ⊗ c' ≅ 𝟙_ C) : D ≌ D :=
  .mk (actionLeft D c) (actionLeft D c')
    ((actionUnitNatIso C D).symm ≪≫ (curriedAction C D).mapIso e.symm ≪≫
      actionLeftTensorIso D c' c)
    ((actionLeftTensorIso D c c').symm ≪≫ (curriedAction C D).mapIso e' ≪≫
      actionUnitNatIso C D)

@[simp]
lemma actionLeftEquivOfIso_functor {c c' : C} (e : c' ⊗ c ≅ 𝟙_ C) (e' : c ⊗ c' ≅ 𝟙_ C) :
    (actionLeftEquivOfIso D e e').functor = actionLeft D c := by
  rfl

@[simp]
lemma actionLeftEquivOfIso_inverse {c c' : C} (e : c' ⊗ c ≅ 𝟙_ C) (e' : c ⊗ c' ≅ 𝟙_ C) :
    (actionLeftEquivOfIso D e e').inverse = actionLeft D c' := by
  rfl

/-- For a left action of a group `G`, the action functor of `g` is an equivalence whose inverse
is the action functor of `g⁻¹`. -/
def actionLeftEquivalence {G : Type*} [Group G] [MonoidalLeftAction (Discrete G) D] (g : G) :
    D ≌ D :=
  actionLeftEquivOfIso D (c := Discrete.mk g) (c' := Discrete.mk g⁻¹)
    (Discrete.eqToIso (inv_mul_cancel g)) (Discrete.eqToIso (mul_inv_cancel g))

@[simp]
lemma actionLeftEquivalence_functor {G : Type*} [Group G]
    [MonoidalLeftAction (Discrete G) D] (g : G) :
    (actionLeftEquivalence D g).functor = actionLeft D (Discrete.mk g) := by
  rfl

@[simp]
lemma actionLeftEquivalence_inverse {G : Type*} [Group G]
    [MonoidalLeftAction (Discrete G) D] (g : G) :
    (actionLeftEquivalence D g).inverse = actionLeft D (Discrete.mk g⁻¹) := by
  rfl

variable {D}

/-- When the acting monoidal category is discrete, the action of a morphism on an object is an
`eqToHom`. -/
lemma actionHomLeft_eq_eqToHom [IsDiscrete C] {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊵ₗ d = eqToHom (by rw [obj_ext_of_isDiscrete f]) := by
  obtain rfl := obj_ext_of_isDiscrete f
  rw [Subsingleton.elim f (𝟙 c)]
  simp

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
