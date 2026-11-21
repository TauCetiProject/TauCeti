/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The homotopy category of a bicategory

The homotopy category of a bicategory `B` has the objects of `B`, and its morphisms `a ⟶ b` are
the isomorphism classes of objects of the hom category `a ⟶ b` of `B`. Composition of
`1`-morphisms descends to these classes by whiskering, and the associators and unitors of `B`
become the category laws.

Categories built from spans or cospans modulo isomorphism of their apices, such as Quillen's
category `Q(E)` of an exact category, arise in this way from a bicategory of spans.

## Main definitions

* `TauCeti.Bicategory.HomotopyCategory B`: a type wrapper for the objects of `B`, with its
  category structure.
* `TauCeti.Bicategory.HomotopyCategory.homMk`: the class of a `1`-morphism.
* `TauCeti.Bicategory.HomotopyCategory.homEquiv`: morphisms of the homotopy category are
  the quotient of `1`-morphisms by the relation of being isomorphic.

## Main statements

* `TauCeti.Bicategory.HomotopyCategory.homMk_eq_homMk_iff`: two `1`-morphisms have the
  same class exactly when they are isomorphic.
* `TauCeti.Bicategory.HomotopyCategory.homMk_comp`: classes compose as `1`-morphisms do.
-/

public section

namespace TauCeti

open CategoryTheory Bicategory

namespace Bicategory

universe w v u

/-- The homotopy category of a bicategory `B`: a type wrapper for the objects of `B`, whose
morphisms are the isomorphism classes of `1`-morphisms of `B`. -/
structure HomotopyCategory (B : Type u) where
  /-- The object of `B` underlying an object of its homotopy category. -/
  as : B

namespace HomotopyCategory

variable {B : Type u} [Bicategory.{w, v} B]

instance : Category.{v} (HomotopyCategory B) where
  Hom X Y := Quotient (isIsomorphicSetoid (X.as ⟶ Y.as))
  id X := ⟦𝟙 X.as⟧
  comp := Quotient.map₂ (· ≫ ·) fun _ _ ⟨e⟩ _ _ ⟨e'⟩ =>
    ⟨whiskerRightIso e _ ≪≫ whiskerLeftIso _ e'⟩
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨λ_ f⟩
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨ρ_ f⟩
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound ⟨α_ f g h⟩

/-- The morphisms of the homotopy category of `B` are the isomorphism classes of
`1`-morphisms of `B`. -/
def homEquiv (X Y : HomotopyCategory B) :
    (X ⟶ Y) ≃ Quotient (isIsomorphicSetoid (X.as ⟶ Y.as)) :=
  Equiv.refl _

/-- The morphism of the homotopy category given by the isomorphism class of a `1`-morphism. -/
def homMk {X Y : HomotopyCategory B} (f : X.as ⟶ Y.as) : X ⟶ Y :=
  (homEquiv X Y).symm ⟦f⟧

@[simp]
theorem homEquiv_homMk {X Y : HomotopyCategory B} (f : X.as ⟶ Y.as) :
    homEquiv X Y (homMk f) = ⟦f⟧ :=
  (homEquiv X Y).apply_symm_apply _

/-- Every morphism of the homotopy category is the class of a `1`-morphism. -/
theorem homMk_surjective {X Y : HomotopyCategory B} :
    Function.Surjective (homMk : (X.as ⟶ Y.as) → (X ⟶ Y)) := by
  intro f
  obtain ⟨g, hg⟩ := Quotient.exists_rep (homEquiv X Y f)
  exact ⟨g, by rw [homMk, hg, Equiv.symm_apply_apply]⟩

/-- Two `1`-morphisms have the same class exactly when they are isomorphic. -/
theorem homMk_eq_homMk_iff {X Y : HomotopyCategory B} {f g : X.as ⟶ Y.as} :
    homMk f = homMk g ↔ Nonempty (f ≅ g) :=
  (homEquiv X Y).symm.injective.eq_iff.trans Quotient.eq

/-- Isomorphic `1`-morphisms have the same class. -/
theorem homMk_eq_homMk {X Y : HomotopyCategory B} {f g : X.as ⟶ Y.as} (e : f ≅ g) :
    homMk f = homMk g :=
  homMk_eq_homMk_iff.2 ⟨e⟩

/-- The identity of the homotopy category is the class of the identity `1`-morphism. -/
@[simp]
theorem homMk_id (X : HomotopyCategory B) : homMk (𝟙 X.as) = 𝟙 X :=
  (rfl)

/-- Composition in the homotopy category is composition of `1`-morphisms. -/
@[simp]
theorem homMk_comp {X Y Z : HomotopyCategory B} (f : X.as ⟶ Y.as) (g : Y.as ⟶ Z.as) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  (rfl)

end HomotopyCategory

end Bicategory

end TauCeti
