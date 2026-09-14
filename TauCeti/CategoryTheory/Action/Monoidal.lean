/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Monoidal

/-!
# Restricting an action along a monoid homomorphism is a monoidal functor

For a monoidal category `V` and a monoid homomorphism `f : G →* H`, Mathlib's
`Action.res V f : Action V H ⥤ Action V G` reindexes an action of `H` along `f`,
keeping the underlying object of `V` and precomposing the action homomorphism with `f`. It is
already known to be additive (`Action.res_additive`). This file records that it is
also **monoidal**, and monoidal in the strictest possible way: restricting a tensor product is
*the same object* as the tensor product of the restrictions, because `(X ⊗ Y).ρ g` is
`X.ρ g ⊗ₘ Y.ρ g` on the nose, so precomposing with `f` distributes over the tensor product without
any comparison map. The unit and the tensorator of `Action.res V f` are therefore identities.

This is the structure a Grothendieck-ring construction needs of a functor before it induces a ring
homomorphism, and it is what makes restriction of representations a homomorphism of representation
rings in `TauCeti/RepresentationTheory/RepresentationRing/Restriction.lean`.

## Main definitions

* `Action.resTensorator`: the tensorator, an identity morphism.
* `Action.resUnitor`: the unit comparison, an identity morphism.
* `Action.resCoreMonoidal`: the two of them packaged as a
  `CategoryTheory.Functor.CoreMonoidal` structure, whence the instance
  `Action.resMonoidal : (Action.res V f).Monoidal`.

## Main statements

* `Action.res_ε_hom`, `Action.res_μ_hom`, `Action.res_η_hom`, `Action.res_δ_hom`: all four
  structure maps of the monoidal functor are identities on the underlying objects of `V`. These
  mirror Mathlib's `Action.forget_ε`, `Action.forget_μ`, `Action.forget_η`, `Action.forget_δ`.

## Implementation notes

The three coherence axioms are proved by simplifying the `Action`-level statement down to `V`,
where the monoidal structure maps of `Action V G` are those of `V`
(`Action.associator_hom_hom` and friends), and then closing the resulting identity in `V`. The
final `exact` restates that identity with `X.V` in place of the definitionally equal
`((Action.res V f).obj X).V`: `simp` cannot perform that replacement itself, because the object
being whiskered by occurs in the *type* of the surrounding composite, but the two are
definitionally equal, so `exact` accepts the tidier form.
-/

public section

universe u w

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Action

variable (V : Type u) [Category.{w} V] [MonoidalCategory V] {G H : Type*} [Monoid G] [Monoid H]
  (f : G →* H)

/-- **The tensorator of restriction along a monoid homomorphism**, the identity: the restriction
of `X ⊗ Y` and the tensor product of the restrictions of `X` and `Y` are the same object of
`Action V G`. -/
def resTensorator (X Y : Action V H) :
    (res V f).obj X ⊗ (res V f).obj Y ≅ (res V f).obj (X ⊗ Y) :=
  mkIso (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm

@[simp]
theorem resTensorator_hom_hom (X Y : Action V H) :
    (resTensorator V f X Y).hom.hom = 𝟙 (X.V ⊗ Y.V) :=
  (rfl)

@[simp]
theorem resTensorator_inv_hom (X Y : Action V H) :
    (resTensorator V f X Y).inv.hom = 𝟙 (X.V ⊗ Y.V) :=
  (rfl)

/-- **The unit comparison of restriction along a monoid homomorphism**, the identity: the
restriction of the tensor unit is the tensor unit. -/
def resUnitor : 𝟙_ (Action V G) ≅ (res V f).obj (𝟙_ (Action V H)) :=
  mkIso (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm

@[simp]
theorem resUnitor_hom_hom : (resUnitor V f).hom.hom = 𝟙 (𝟙_ V) :=
  (rfl)

@[simp]
theorem resUnitor_inv_hom : (resUnitor V f).inv.hom = 𝟙 (𝟙_ V) :=
  (rfl)

/-- Restriction along a monoid homomorphism, as a `CategoryTheory.Functor.CoreMonoidal`: the unit
and the tensorator are the identities of `Action.resUnitor` and `Action.resTensorator`, and the
three coherence axioms reduce to the corresponding identities in `V`. -/
def resCoreMonoidal : (res V f).CoreMonoidal where
  εIso := resUnitor V f
  μIso := resTensorator V f
  μIso_hom_natural_left _ _ := by
    apply hom_ext; exact (Category.comp_id _).trans (Category.id_comp _).symm
  μIso_hom_natural_right _ _ := by
    apply hom_ext; exact (Category.comp_id _).trans (Category.id_comp _).symm
  associativity X Y Z := by
    apply hom_ext
    simp only [tensorObj_V, comp_hom, whiskerRight_hom, resTensorator_hom_hom, res_map_hom,
      associator_hom_hom, whiskerLeft_hom]
    exact (show 𝟙 (X.V ⊗ Y.V) ▷ Z.V ≫ 𝟙 ((X.V ⊗ Y.V) ⊗ Z.V) ≫ (α_ X.V Y.V Z.V).hom =
        (α_ X.V Y.V Z.V).hom ≫ X.V ◁ 𝟙 (Y.V ⊗ Z.V) ≫ 𝟙 (X.V ⊗ Y.V ⊗ Z.V) by simp)
  left_unitality X := by
    apply hom_ext
    simp only [tensorObj_V, tensorUnit_V, leftUnitor_hom_hom, comp_hom, whiskerRight_hom,
      resUnitor_hom_hom, resTensorator_hom_hom, res_map_hom]
    exact (show (λ_ X.V).hom = 𝟙 (𝟙_ V) ▷ X.V ≫ 𝟙 (𝟙_ V ⊗ X.V) ≫ (λ_ X.V).hom by simp)
  right_unitality X := by
    apply hom_ext
    simp only [tensorObj_V, tensorUnit_V, rightUnitor_hom_hom, comp_hom, whiskerLeft_hom,
      resUnitor_hom_hom, resTensorator_hom_hom, res_map_hom]
    exact (show (ρ_ X.V).hom = X.V ◁ 𝟙 (𝟙_ V) ≫ 𝟙 (X.V ⊗ 𝟙_ V) ≫ (ρ_ X.V).hom by simp)

/-- **Restriction of an action along a monoid homomorphism is a monoidal functor.** -/
instance resMonoidal : (res V f).Monoidal :=
  (resCoreMonoidal V f).toMonoidal

@[simp]
theorem res_ε_hom : (ε (res V f)).hom = 𝟙 (𝟙_ V) :=
  (rfl)

@[simp]
theorem res_η_hom : (η (res V f)).hom = 𝟙 (𝟙_ V) :=
  (rfl)

@[simp]
theorem res_μ_hom (X Y : Action V H) : (μ (res V f) X Y).hom = 𝟙 (X.V ⊗ Y.V) :=
  (rfl)

@[simp]
theorem res_δ_hom (X Y : Action V H) : (δ (res V f) X Y).hom = 𝟙 (X.V ⊗ Y.V) :=
  (rfl)

end Action
