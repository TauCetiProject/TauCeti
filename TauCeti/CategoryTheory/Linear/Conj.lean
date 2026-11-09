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

variable (R) in
/-- Conjugation by an isomorphism identifies endomorphism algebras in a linear category. -/
def conjAlgEquiv (e : X ≅ Y) : End X ≃ₐ[R] End Y where
  __ := e.conj
  map_add' f g := by ext; simp
  commutes' r := by ext; simp

/-- The underlying multiplicative equivalence is Mathlib's conjugation equivalence. -/
@[simp]
theorem conjAlgEquiv_toMulEquiv (e : X ≅ Y) :
    (e.conjAlgEquiv R).toMulEquiv = e.conj := (rfl)

/-- Applying the algebra equivalence is applying Mathlib's conjugation equivalence. -/
@[simp]
theorem conjAlgEquiv_apply (e : X ≅ Y) (f : End X) :
    e.conjAlgEquiv R f = e.conj f := (rfl)

/-- Conjugation by the identity is the identity algebra equivalence. -/
@[simp]
theorem refl_conjAlgEquiv : (Iso.refl X).conjAlgEquiv R = AlgEquiv.refl := by
  ext f
  simp

/-- Conjugating successively agrees with conjugation by the composite. -/
@[simp]
theorem trans_conjAlgEquiv (e : X ≅ Y) (f : Y ≅ Z) :
    (e ≪≫ f).conjAlgEquiv R = (e.conjAlgEquiv R).trans (f.conjAlgEquiv R) := by
  ext g
  simp

/-- Reversing the isomorphism reverses the induced algebra equivalence. -/
@[simp]
theorem symm_conjAlgEquiv (e : X ≅ Y) :
    e.symm.conjAlgEquiv R = (e.conjAlgEquiv R).symm := by
  ext f
  rfl

end CategoryTheory.Iso
