/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The 1-truncation of a bicategory

Every bicategory `B` has an underlying category `Truncation B` with the same objects, whose
morphisms `a ⟶ b` are the isomorphism classes of 1-morphisms `a ⟶ b` in `B`. Composition is
induced by composition of 1-morphisms: whiskering carries 2-isomorphisms to 2-isomorphisms, the
associator makes it associative and the unitors make the classes of identities into identities.

This is how categories whose morphisms are spans or cospans up to isomorphism of their apex,
such as Quillen's `Q`-construction of an exact category, arise from Mathlib's span bicategory.

## Main definitions

* `TauCeti.CategoryTheory.Bicategory.Truncation B`: the 1-truncation of the bicategory `B`.
* `TauCeti.CategoryTheory.Bicategory.Truncation.homMk`: the class of a 1-morphism.
* `TauCeti.CategoryTheory.Bicategory.Truncation.homLift`: a function on 1-morphisms invariant
  under isomorphism, descended to the truncation.

## Main results

* `TauCeti.CategoryTheory.Bicategory.Truncation.homMk_eq_homMk_iff`: two 1-morphisms have the
  same class exactly when they are isomorphic.
* `TauCeti.CategoryTheory.Bicategory.Truncation.homMk_comp` and
  `TauCeti.CategoryTheory.Bicategory.Truncation.homMk_id`: the class of a composite is the
  composite of the classes, and the class of an identity is an identity.
-/

public section

namespace TauCeti.CategoryTheory.Bicategory

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

/-- The 1-truncation of a bicategory `B`: the category with the objects of `B` whose morphisms
are the isomorphism classes of 1-morphisms of `B`. -/
structure Truncation (B : Type u) where
  /-- The object of `B` underlying an object of the truncation. -/
  as : B

namespace Truncation

variable {B : Type u} [Bicategory.{w, v} B]

/-- The category structure on the 1-truncation: morphisms are isomorphism classes of
1-morphisms, composed by composing representatives. -/
instance : Category.{v} (Truncation B) where
  Hom a b := Quotient (isIsomorphicSetoid (a.as ⟶ b.as))
  id a := ⟦𝟙 a.as⟧
  comp := Quotient.map₂ (· ≫ ·) fun _ f' ⟨e⟩ g _ ⟨e'⟩ =>
    ⟨whiskerRightIso e g ≪≫ whiskerLeftIso f' e'⟩
  id_comp := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound ⟨λ_ f⟩
  comp_id := by
    rintro _ _ ⟨f⟩
    exact Quotient.sound ⟨ρ_ f⟩
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound ⟨α_ f g h⟩

/-- The class of a 1-morphism `f : a ⟶ b` of `B`, as a morphism of the 1-truncation. -/
def homMk {a b : B} (f : a ⟶ b) : (⟨a⟩ : Truncation B) ⟶ ⟨b⟩ :=
  (⟦f⟧ : Quotient (isIsomorphicSetoid (a ⟶ b)))

/-- Two 1-morphisms have the same class in the truncation exactly when they are isomorphic. -/
theorem homMk_eq_homMk_iff {a b : B} {f g : a ⟶ b} : homMk f = homMk g ↔ Nonempty (f ≅ g) :=
  Quotient.eq

/-- Isomorphic 1-morphisms have the same class in the truncation. -/
theorem homMk_eq_of_iso {a b : B} {f g : a ⟶ b} (e : f ≅ g) : homMk f = homMk g :=
  homMk_eq_homMk_iff.2 ⟨e⟩

/-- Every morphism of the truncation is the class of a 1-morphism. -/
theorem homMk_surjective {a b : Truncation B} (φ : a ⟶ b) : ∃ f : a.as ⟶ b.as, homMk f = φ :=
  Quotient.exists_rep φ

/-- Induction principle for morphisms of the truncation: a property holding for the class of
every 1-morphism holds for every morphism. -/
@[elab_as_elim]
theorem hom_induction {a b : Truncation B} {motive : (a ⟶ b) → Prop}
    (h : ∀ f : a.as ⟶ b.as, motive (homMk f)) (φ : a ⟶ b) : motive φ :=
  Quotient.ind h φ

/-- A function on 1-morphisms `a ⟶ b` that takes the same value on isomorphic 1-morphisms
descends to the morphisms of the truncation. -/
def homLift {a b : B} {α : Sort*} (F : (a ⟶ b) → α) (hF : ∀ ⦃f g : a ⟶ b⦄, (f ≅ g) → F f = F g) :
    ((⟨a⟩ : Truncation B) ⟶ ⟨b⟩) → α :=
  Quotient.lift F fun _ _ ⟨e⟩ => hF e

@[simp]
theorem homLift_homMk {a b : B} {α : Sort*} (F : (a ⟶ b) → α)
    (hF : ∀ ⦃f g : a ⟶ b⦄, (f ≅ g) → F f = F g) (f : a ⟶ b) : homLift F hF (homMk f) = F f :=
  (rfl)

/-- The class of an identity 1-morphism is an identity. -/
@[simp]
theorem homMk_id (a : B) : homMk (𝟙 a) = 𝟙 (⟨a⟩ : Truncation B) :=
  (rfl)

/-- The class of a composite is the composite of the classes. -/
@[simp]
theorem homMk_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  (rfl)

end Truncation

end TauCeti.CategoryTheory.Bicategory
