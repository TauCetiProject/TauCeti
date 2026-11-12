/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Dagger categories

A dagger is chosen identity-on-objects, contravariant involutive data on a native category.
Additive and conjugate-linear compatibility are separate properties of this data; in particular,
none of these interfaces imposes norm, completeness, or positivity assumptions.

Unitary arrows have their dagger as a two-sided inverse. They compose, and define native
categorical isomorphisms. Endomorphisms inherit the usual algebraic star structures, with
Mathlib's operator-order multiplication on `CategoryTheory.End`.
-/

public section

open CategoryTheory

universe w v u

namespace TauCeti

/-- An identity-on-objects contravariant involution on a category. -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The dagger reverses the direction of an arrow. -/
  dagger : {X Y : C} → (X ⟶ Y) → (Y ⟶ X)
  /-- The dagger fixes identity arrows. -/
  dagger_id : ∀ X : C, dagger (𝟙 X) = 𝟙 X
  /-- The dagger reverses composition. -/
  dagger_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    dagger (f ≫ g) = dagger g ≫ dagger f
  /-- Applying the dagger twice recovers the original arrow. -/
  dagger_dagger : ∀ {X Y : C} (f : X ⟶ Y), dagger (dagger f) = f

export DaggerCategory (dagger dagger_id dagger_comp dagger_dagger)

attribute [simp] dagger_id dagger_comp dagger_dagger

namespace Dagger

/-- Postfix notation for the chosen dagger. -/
scoped postfix:max "†" => TauCeti.DaggerCategory.dagger

end Dagger

variable {C : Type u} [Category.{v} C] [DaggerCategory C]
variable {W X Y Z : C}

/-- Taking daggers is a bijection between opposite Hom spaces. -/
def daggerEquiv (X Y : C) : (X ⟶ Y) ≃ (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger

/-- Evaluation of the dagger bijection. -/
@[simp] theorem daggerEquiv_apply (f : X ⟶ Y) : daggerEquiv X Y f = dagger f := (rfl)

/-- The inverse dagger bijection also takes daggers. -/
@[simp] theorem daggerEquiv_symm_apply (f : Y ⟶ X) :
    (daggerEquiv X Y).symm f = dagger f := (rfl)

/-- Taking daggers detects equality. -/
@[simp] theorem dagger_inj {f g : X ⟶ Y} : dagger f = dagger g ↔ f = g :=
  (daggerEquiv X Y).injective.eq_iff

/-- Additive compatibility of the chosen dagger on a preadditive category. -/
class DaggerPreadditive (C : Type u) [Category.{v} C] [DaggerCategory C]
    [Preadditive C] : Prop where
  /-- Taking daggers commutes with addition. -/
  dagger_add : ∀ {X Y : C} (f g : X ⟶ Y), dagger (f + g) = dagger f + dagger g

export DaggerPreadditive (dagger_add)
attribute [simp] dagger_add

section Preadditive

variable [Preadditive C] [DaggerPreadditive C]

/-- The dagger as an additive equivalence of Hom groups. -/
def daggerAddEquiv (X Y : C) : (X ⟶ Y) ≃+ (Y ⟶ X) where
  toEquiv := daggerEquiv X Y
  map_add' := dagger_add

/-- Evaluation of the additive dagger equivalence. -/
@[simp] theorem daggerAddEquiv_apply (f : X ⟶ Y) :
    daggerAddEquiv X Y f = dagger f := (rfl)

/-- The dagger fixes the zero arrow. -/
@[simp] theorem dagger_zero : dagger (0 : X ⟶ Y) = 0 :=
  (daggerAddEquiv X Y).map_zero

/-- The dagger commutes with negation. -/
@[simp] theorem dagger_neg (f : X ⟶ Y) : dagger (-f) = -dagger f :=
  (daggerAddEquiv X Y).map_neg f

/-- The dagger commutes with subtraction. -/
@[simp] theorem dagger_sub (f g : X ⟶ Y) : dagger (f - g) = dagger f - dagger g :=
  (daggerAddEquiv X Y).map_sub f g

end Preadditive

/-- Conjugate-scalar compatibility for a dagger on a native linear category.
The scalar involution is arbitrary; complex conjugation is its standard specialization. -/
class DaggerLinear (R : Type w) [CommSemiring R] [StarRing R]
    (C : Type u) [Category.{v} C] [DaggerCategory C] [Preadditive C]
    [Linear R C] : Prop where
  /-- Taking daggers conjugates the scalar. -/
  dagger_smul : ∀ {X Y : C} (r : R) (f : X ⟶ Y),
    dagger (r • f) = star r • dagger f

export DaggerLinear (dagger_smul)
attribute [simp] dagger_smul

/-- An arrow is unitary when its dagger is its two-sided inverse. -/
def IsUnitary (f : X ⟶ Y) : Prop :=
  f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y

/-- The two inverse equations characterize a unitary arrow. -/
theorem isUnitary_iff (f : X ⟶ Y) :
    IsUnitary f ↔ f ≫ dagger f = 𝟙 X ∧ dagger f ≫ f = 𝟙 Y := Iff.rfl

namespace IsUnitary

/-- A unitary arrow composed with its dagger is the identity. -/
@[simp, reassoc] theorem hom_dagger_id {f : X ⟶ Y} (hf : IsUnitary f) :
    f ≫ dagger f = 𝟙 X := hf.1

/-- The dagger of a unitary arrow composed with that arrow is the identity. -/
@[simp, reassoc] theorem dagger_hom_id {f : X ⟶ Y} (hf : IsUnitary f) :
    dagger f ≫ f = 𝟙 Y := hf.2

/-- Identity arrows are unitary. -/
@[simp] theorem id (X : C) : IsUnitary (𝟙 X) := by
  simp [isUnitary_iff]

/-- The dagger of a unitary arrow is unitary. -/
theorem dagger {f : X ⟶ Y} (hf : IsUnitary f) : IsUnitary (TauCeti.dagger f) := by
  simpa only [isUnitary_iff, dagger_dagger] using And.intro hf.2 hf.1

/-- Composites of unitary arrows are unitary. -/
theorem comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ≫ g) := by
  constructor <;> simp [Category.assoc, hg.hom_dagger_id_assoc, hf.dagger_hom_id_assoc,
    hf.hom_dagger_id, hg.dagger_hom_id]

/-- A unitary arrow determines an isomorphism whose inverse is its dagger. -/
def toIso {f : X ⟶ Y} (hf : IsUnitary f) : X ≅ Y where
  hom := f
  inv := TauCeti.dagger f
  hom_inv_id := hf.1
  inv_hom_id := hf.2

/-- The isomorphism of a unitary arrow has the original arrow as its forward map. -/
@[simp] theorem toIso_hom {f : X ⟶ Y} (hf : IsUnitary f) : hf.toIso.hom = f := (rfl)

/-- The isomorphism of a unitary arrow has the dagger as its inverse. -/
@[simp] theorem toIso_inv {f : X ⟶ Y} (hf : IsUnitary f) :
    hf.toIso.inv = TauCeti.dagger f := (rfl)

end IsUnitary

/-- Taking the dagger preserves and reflects unitarity. -/
@[simp] theorem isUnitary_dagger_iff (f : X ⟶ Y) : IsUnitary (dagger f) ↔ IsUnitary f :=
  ⟨fun h => by simpa using h.dagger, IsUnitary.dagger⟩

end TauCeti

namespace CategoryTheory.Iso

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X Y : C}

/-- An isomorphism is unitary precisely when its inverse is its dagger. -/
theorem isUnitary_hom_iff (e : X ≅ Y) : IsUnitary e.hom ↔ dagger e.hom = e.inv := by
  constructor
  · intro h
    exact (cancel_epi e.hom).mp (h.1.trans e.hom_inv_id.symm)
  · intro h
    simp [isUnitary_iff, h]

/-- The inverse of a unitary isomorphism is its dagger. -/
theorem dagger_hom (e : X ≅ Y) (h : IsUnitary e.hom) : dagger e.hom = e.inv :=
  e.isUnitary_hom_iff.mp h

end CategoryTheory.Iso

namespace CategoryTheory.End

open TauCeti

variable {C : Type u} [Category.{v} C] [DaggerCategory C] {X : C}

/-- The dagger is the star operation on endomorphisms. -/
instance daggerStar : Star (End X) where
  star f := .of (dagger f.asHom)

/-- The endomorphism star acts by the dagger on its underlying arrow. -/
@[simp] theorem star_asHom (f : End X) : (star f).asHom = dagger f.asHom := (rfl)

/-- The endomorphism dagger is involutive. -/
instance daggerInvolutiveStar : InvolutiveStar (End X) where
  star_involutive f := by ext; simp

/-- Operator-order multiplication makes endomorphisms a star monoid. -/
instance daggerStarMul : StarMul (End X) where
  star_mul f g := by ext; simp

/-- In an additive dagger category the endomorphism ring is a star ring. -/
instance [Preadditive C] [DaggerPreadditive C] : StarRing (End X) where
  star_add f g := by ext; simp

/-- The scalar action on endomorphisms is compatible with the dagger involution. -/
instance {R : Type w} [CommSemiring R] [StarRing R] [Preadditive C] [Linear R C]
    [DaggerLinear R C] : StarModule R (End X) where
  star_smul r f := by ext; simp

end CategoryTheory.End
