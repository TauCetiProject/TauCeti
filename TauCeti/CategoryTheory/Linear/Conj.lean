/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Conj
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Conjugation of endomorphism algebras

An isomorphism in a linear category identifies the endomorphism algebras of its
source and target. This upgrades Mathlib's `CategoryTheory.Iso.conj` to an algebra
equivalence, so that changing an object preserves the full coefficient algebra.
-/

public section

namespace CategoryTheory.Iso

variable {R C : Type*} [CommSemiring R] [Category* C] [Preadditive C] [Linear R C]
  {X Y Z : C}

/-- Conjugation by an isomorphism identifies endomorphism algebras in a linear category. -/
def conjAlgEquiv (e : X ≅ Y) : End X ≃ₐ[R] End Y where
  __ := e.conj
  map_add' f g := by ext; simp
  commutes' r := by ext; simp

/-- The underlying morphism is conjugated by the specified isomorphism. -/
@[simp]
theorem conjAlgEquiv_asHom (e : X ≅ Y) (f : End X) :
    (e.conjAlgEquiv (R := R) f).asHom = e.inv ≫ f.asHom ≫ e.hom := (rfl)

/-- Conjugation by the identity is the identity algebra equivalence. -/
@[simp]
theorem refl_conjAlgEquiv : (Iso.refl X).conjAlgEquiv (R := R) = AlgEquiv.refl := by
  ext f
  simp

/-- Conjugating successively agrees with conjugation by the composite. -/
@[simp]
theorem trans_conjAlgEquiv (e : X ≅ Y) (f : Y ≅ Z) :
    (e ≪≫ f).conjAlgEquiv (R := R) = e.conjAlgEquiv.trans f.conjAlgEquiv := by
  ext g
  simp

/-- Reversing the isomorphism reverses the induced algebra equivalence. -/
@[simp]
theorem symm_conjAlgEquiv (e : X ≅ Y) :
    e.symm.conjAlgEquiv (R := R) = e.conjAlgEquiv.symm := by
  ext f
  rfl

end CategoryTheory.Iso
