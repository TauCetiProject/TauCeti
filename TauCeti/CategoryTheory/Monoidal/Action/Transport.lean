/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Transporting a monoidal left action along an equivalence

Let a monoidal category `C` act on the left on a category `D`, and let `e : D ≌ D'` be an
equivalence of categories. Then `C` acts on `D'` by conjugating with `e`:
`c ⊙ₗ X = e.functor.obj (c ⊙ₗ e.inverse.obj X)`, with the associator and unitor of `D` conjugated
by `e` and corrected by the unit and counit of `e`. This file constructs this action and shows
that `e` becomes an equivalence of categories with an action.

* `CategoryTheory.Equivalence.transportMonoidalLeftAction C e` is the transported action of `C`
  on `D'`. For a group `G`, it transports a categorical action of `G` (an action of
  `Discrete G`) along an equivalence, for instance from one presentation of a representation
  category to an equivalent one.
* `CategoryTheory.Equivalence.functorLeftLinearOfTransport C e` makes `e.functor` left-linear for
  the transported action, with lineators `e.functor.map (c ⊴ₗ e.unitInv.app X)`. Combined with
  `Equivalence.inverseLeftLinear`, the inverse functor is left-linear too, with lineators the
  components `e.unit.app (c ⊙ₗ e.inverse.obj X)` of the unit
  (`Equivalence.inverseLeftLinear_μₗ_transport`), and the unit and counit of `e` are left-linear
  by `Equivalence.isLeftLinear_unit` and `Equivalence.isLeftLinear_counit`.
* `CategoryTheory.Equivalence.actionLeftTransportIso` identifies the transported action functor
  of `c` with `e.inverse ⋙ actionLeft D c ⋙ e.functor`, with identity components. Consequently,
  if the action functors on a preadditive category `D` are additive or `R`-linear and `e` is
  additive or `R`-linear, so are the transported action functors.

This is the analogue for actions of Mathlib's transport of a monoidal structure along an
equivalence, `CategoryTheory.Monoidal.transport`.
-/

public section

namespace CategoryTheory.Equivalence

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable (C : Type*) [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalLeftAction C D] {D' : Type*} [Category* D']

/-- The data of the left action of `C` on `D'` transported along an equivalence `e : D ≌ D'`:
`c ⊙ₗ X = e.functor.obj (c ⊙ₗ e.inverse.obj X)`. -/
@[expose, instance_reducible]
def transportMonoidalLeftActionStruct (e : D ≌ D') : MonoidalLeftActionStruct C D' where
  actionObj c X := e.functor.obj (c ⊙ₗ e.inverse.obj X)
  actionHomLeft f X := e.functor.map (f ⊵ₗ e.inverse.obj X)
  actionHomRight c _ _ g := e.functor.map (c ⊴ₗ e.inverse.map g)
  actionHom f g := e.functor.map (f ⊙ₗₘ e.inverse.map g)
  actionAssocIso c c' X :=
    { hom := e.functor.map ((αₗ c c' (e.inverse.obj X)).hom ≫ c ⊴ₗ e.unit.app _)
      inv := e.functor.map (c ⊴ₗ e.unitInv.app _ ≫ (αₗ c c' (e.inverse.obj X)).inv)
      hom_inv_id := by simp [← Functor.map_comp, ← actionHomRight_comp_assoc]
      inv_hom_id := by simp [← Functor.map_comp, ← actionHomRight_comp] }
  actionUnitIso X :=
    { hom := e.functor.map (λₗ (e.inverse.obj X)).hom ≫ e.counit.app X
      inv := e.counitInv.app X ≫ e.functor.map (λₗ (e.inverse.obj X)).inv
      hom_inv_id := by simp
      inv_hom_id := by simp }

/-- The left action of `C` on `D'` transported along an equivalence `e : D ≌ D'`. Its action on
objects is `c ⊙ₗ X = e.functor.obj (c ⊙ₗ e.inverse.obj X)`, its associator is conjugated from
that of `D` and corrected by the unit of `e`, and its unitor is conjugated from that of `D` and
corrected by the counit of `e`. -/
@[expose, instance_reducible]
def transportMonoidalLeftAction (e : D ≌ D') : MonoidalLeftAction C D' where
  toMonoidalLeftActionStruct := transportMonoidalLeftActionStruct C e
  actionHom_def f g := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp [← Functor.map_comp, actionHom_def]
  actionHomRight_id c X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp
  id_actionHomLeft c X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp
  actionHom_comp f₁ f₂ g₁ g₂ := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp
  actionAssocIso_hom_naturality f g h := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    simp [actionAssocIso_hom_naturality_assoc, ← id_actionHom, ← actionHom_comp]
  actionUnitIso_hom_naturality f := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp
  whiskerLeft_actionHomLeft c f X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp only [← Functor.map_comp, Category.assoc]
    simp [-actionHomRight_comp, ← actionHomRight_comp_assoc]
  whiskerRight_actionHomLeft c f X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    rw [action_exchange_assoc, whiskerRight_actionHomLeft]
    simp [← actionHomRight_comp_assoc]
  associator_actionHom c₁ c₂ c₃ X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    simp [← actionHomRight_comp, ← associator_actionHom_assoc]
  leftUnitor_actionHom c X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp
  rightUnitor_actionHom c X := by
    dsimp +instances only [transportMonoidalLeftActionStruct]
    simp only [← Functor.map_comp, Category.assoc]
    congr 1
    simp [← actionHomRight_comp]

variable (e : D ≌ D')

section Formulas

variable {C}

lemma transportMonoidalLeftAction_actionObj (c : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    c ⊙ₗ X = e.functor.obj (c ⊙ₗ e.inverse.obj X) :=
  rfl

lemma transportMonoidalLeftAction_actionHomLeft {c c' : C} (f : c ⟶ c') (X : D') :
    letI := e.transportMonoidalLeftAction C
    f ⊵ₗ X = e.functor.map (f ⊵ₗ e.inverse.obj X) :=
  rfl

lemma transportMonoidalLeftAction_actionHomRight (c : C) {X Y : D'} (g : X ⟶ Y) :
    letI := e.transportMonoidalLeftAction C
    c ⊴ₗ g = e.functor.map (c ⊴ₗ e.inverse.map g) :=
  rfl

lemma transportMonoidalLeftAction_actionHom {c c' : C} {X Y : D'} (f : c ⟶ c') (g : X ⟶ Y) :
    letI := e.transportMonoidalLeftAction C
    f ⊙ₗₘ g = e.functor.map (f ⊙ₗₘ e.inverse.map g) :=
  rfl

lemma transportMonoidalLeftAction_actionAssocIso_hom (c c' : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    (αₗ c c' X).hom =
      e.functor.map ((αₗ c c' (e.inverse.obj X)).hom ≫ c ⊴ₗ e.unit.app (c' ⊙ₗ e.inverse.obj X)) :=
  rfl

lemma transportMonoidalLeftAction_actionAssocIso_inv (c c' : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    (αₗ c c' X).inv =
      e.functor.map
        (c ⊴ₗ e.unitInv.app (c' ⊙ₗ e.inverse.obj X) ≫ (αₗ c c' (e.inverse.obj X)).inv) :=
  rfl

lemma transportMonoidalLeftAction_actionUnitIso_hom (X : D') :
    letI := e.transportMonoidalLeftAction C
    (λₗ[C] X).hom = e.functor.map (λₗ[C] (e.inverse.obj X)).hom ≫ e.counit.app X :=
  rfl

lemma transportMonoidalLeftAction_actionUnitIso_inv (X : D') :
    letI := e.transportMonoidalLeftAction C
    (λₗ[C] X).inv = e.counitInv.app X ≫ e.functor.map (λₗ[C] (e.inverse.obj X)).inv :=
  rfl

end Formulas

/-- For the transported action `e.transportMonoidalLeftAction C`, the functor of `e` is
left-linear, with lax lineators `e.functor.map (c ⊴ₗ e.unitInv.app X)` and oplax lineators
`e.functor.map (c ⊴ₗ e.unit.app X)`. -/
@[expose, instance_reducible]
def functorLeftLinearOfTransport :
    letI := e.transportMonoidalLeftAction C
    e.functor.LeftLinear C :=
  letI := e.transportMonoidalLeftAction C
  { μₗ c X := e.functor.map (c ⊴ₗ e.unitInv.app X)
    δₗ c X := e.functor.map (c ⊴ₗ e.unit.app X)
    μₗ_naturality_left f X := by
      simp [transportMonoidalLeftAction_actionHomLeft, ← Functor.map_comp, action_exchange]
    μₗ_naturality_right c X Y g := by
      simp [transportMonoidalLeftAction_actionHomRight, ← Functor.map_comp,
        -actionHomRight_comp, ← actionHomRight_comp]
    μₗ_associativity c c' X := by
      simp [transportMonoidalLeftAction_actionAssocIso_hom,
        transportMonoidalLeftAction_actionHomRight, ← Functor.map_comp, -actionHomRight_comp,
        ← actionHomRight_comp]
    μₗ_unitality X := by
      simp [transportMonoidalLeftAction_actionUnitIso_hom, counit_app_functor]
    δₗ_naturality_left f X := by
      simp [transportMonoidalLeftAction_actionHomLeft, ← Functor.map_comp, action_exchange]
    δₗ_naturality_right c X Y g := by
      simp [transportMonoidalLeftAction_actionHomRight, ← Functor.map_comp,
        -actionHomRight_comp, ← actionHomRight_comp]
    δₗ_associativity c c' X := by
      simp [transportMonoidalLeftAction_actionAssocIso_hom,
        transportMonoidalLeftAction_actionHomRight, ← Functor.map_comp, -actionHomRight_comp,
        ← actionHomRight_comp]
    δₗ_unitality_inv X := by
      simp [transportMonoidalLeftAction_actionUnitIso_inv, counitInv_app_functor]
    μₗ_comp_δₗ c X := by
      rw [← Functor.map_comp, ← actionHomRight_comp, Iso.inv_hom_id_app]
      -- The two identities agree since `c ⊙ₗ e.functor.obj X` is by definition
      -- `e.functor.obj (c ⊙ₗ e.inverse.obj (e.functor.obj X))`.
      exact (congrArg e.functor.map (actionHomRight_id c _)).trans (e.functor.map_id _)
    δₗ_comp_μₗ c X := by simp [← Functor.map_comp, ← actionHomRight_comp] }

section Lineators

variable {C}

/-- The lax lineators of `e.functorLeftLinearOfTransport C`. -/
lemma functorLeftLinearOfTransport_μₗ (c : C) (X : D) :
    letI := e.transportMonoidalLeftAction C
    letI := e.functorLeftLinearOfTransport C
    μₗ e.functor c X = e.functor.map (c ⊴ₗ e.unitInv.app X) :=
  rfl

/-- The oplax lineators of `e.functorLeftLinearOfTransport C`. -/
lemma functorLeftLinearOfTransport_δₗ (c : C) (X : D) :
    letI := e.transportMonoidalLeftAction C
    letI := e.functorLeftLinearOfTransport C
    δₗ e.functor c X = e.functor.map (c ⊴ₗ e.unit.app X) :=
  rfl

/-- For the transported action, the left-linear structure `e.inverseLeftLinear C` that the
inverse functor inherits from `e.functorLeftLinearOfTransport C` has as lax lineators the
components of the unit of `e`. -/
lemma inverseLeftLinear_μₗ_transport (c : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    letI := e.functorLeftLinearOfTransport C
    letI := e.inverseLeftLinear C
    μₗ e.inverse c X = e.unit.app (c ⊙ₗ e.inverse.obj X) := by
  let := e.transportMonoidalLeftAction C
  let := e.functorLeftLinearOfTransport C
  rw [inverseLeftLinear_μₗ, functorLeftLinearOfTransport_δₗ,
    transportMonoidalLeftAction_actionHomRight]
  simp [-actionHomRight_comp, ← actionHomRight_comp_assoc]

end Lineators

section Linear

variable {C}

/-- The transported action functor of `c` is the conjugate
`e.inverse ⋙ actionLeft D c ⋙ e.functor` of the action functor of `c` on `D`, with identity
components. -/
def actionLeftTransportIso (c : C) :
    letI := e.transportMonoidalLeftAction C
    actionLeft D' c ≅ e.inverse ⋙ actionLeft D c ⋙ e.functor :=
  -- By definition of the transported action, both functors send `X` to
  -- `e.functor.obj (c ⊙ₗ e.inverse.obj X)` and `f` to `e.functor.map (c ⊴ₗ e.inverse.map f)`.
  letI := e.transportMonoidalLeftAction C
  Iso.refl _

@[simp]
lemma actionLeftTransportIso_hom_app (c : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    (actionLeftTransportIso e c).hom.app X = 𝟙 (e.functor.obj (c ⊙ₗ e.inverse.obj X)) := by
  rfl

@[simp]
lemma actionLeftTransportIso_inv_app (c : C) (X : D') :
    letI := e.transportMonoidalLeftAction C
    (actionLeftTransportIso e c).inv.app X = 𝟙 (e.functor.obj (c ⊙ₗ e.inverse.obj X)) := by
  rfl

variable [Preadditive D] [Preadditive D'] (c : C)

/-- If the action of `c` on a preadditive category `D` is additive and `e.functor` is additive,
the transported action of `c` on `D'` is additive. -/
lemma additive_actionLeft_transport [e.functor.Additive] [(actionLeft D c).Additive] :
    letI := e.transportMonoidalLeftAction C
    (actionLeft D' c).Additive :=
  letI := e.transportMonoidalLeftAction C
  Functor.additive_of_iso (actionLeftTransportIso e c).symm

/-- If the action of `c` on a preadditive category `D` is `R`-linear and `e.functor` is
`R`-linear, the transported action of `c` on `D'` is `R`-linear. -/
lemma linear_actionLeft_transport (R : Type*) [Semiring R] [Linear R D] [Linear R D']
    [e.functor.Linear R] [(actionLeft D c).Linear R] :
    letI := e.transportMonoidalLeftAction C
    (actionLeft D' c).Linear R :=
  letI := e.transportMonoidalLeftAction C
  Functor.linear_of_iso R (actionLeftTransportIso e c).symm

end Linear

end CategoryTheory.Equivalence
