/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Endomorphism rings under isomorphisms and additive functors

In a preadditive category, isomorphic objects have isomorphic endomorphism rings: conjugation
`Iso.conj` is additive. An additive functor `F` induces a ring homomorphism
`End X →+* End (F.obj X)`, refining the monoid homomorphism `Functor.mapEnd`, and it is surjective
when `F` is full.

## Main definitions

* `CategoryTheory.Iso.endRingEquiv`: the ring isomorphism `End X ≃+* End Y` induced by `X ≅ Y`.
* `CategoryTheory.Functor.mapEndRingHom`: the ring homomorphism `End X →+* End (F.obj X)` of an
  additive functor.

## Main results

* `CategoryTheory.Iso.endRingEquiv_apply_asHom` and
  `CategoryTheory.Functor.mapEndRingHom_apply_asHom`: the underlying morphisms.
* `CategoryTheory.Functor.mapEndRingHom_surjective`: a full additive functor is surjective on
  endomorphism rings.
-/

public section

namespace CategoryTheory.Iso

variable {C : Type*} [Category* C] [Preadditive C]

/-- Isomorphic objects have isomorphic endomorphism rings: `Iso.conj` is additive. -/
def endRingEquiv {X Y : C} (φ : X ≅ Y) : End X ≃+* End Y where
  __ := φ.conj
  map_add' f g := by ext; simp

/-- The ring isomorphism of `φ : X ≅ Y` conjugates an endomorphism by `φ`. -/
@[simp]
theorem endRingEquiv_apply_asHom {X Y : C} (φ : X ≅ Y) (f : End X) :
    (φ.endRingEquiv f).asHom = φ.inv ≫ f.asHom ≫ φ.hom := by
  simp [endRingEquiv]

end CategoryTheory.Iso

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- An additive functor induces a ring homomorphism on endomorphism rings, refining
`CategoryTheory.Functor.mapEnd`. -/
def mapEndRingHom (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := by ext; simp [mapEnd]
  map_add' f g := by ext; simp [mapEnd]

/-- The ring homomorphism of an additive functor applies the functor to an endomorphism. -/
@[simp]
theorem mapEndRingHom_apply_asHom (F : C ⥤ D) [F.Additive] (X : C) (f : End X) :
    (F.mapEndRingHom X f).asHom = F.map f.asHom := by
  simp [mapEndRingHom, mapEnd]

/-- A full additive functor induces a surjection on endomorphism rings. -/
theorem mapEndRingHom_surjective (F : C ⥤ D) [F.Additive] [F.Full] (X : C) :
    Function.Surjective (F.mapEndRingHom X) := fun f ↦
  ⟨End.of (F.preimage f.asHom), by ext; simp⟩

end CategoryTheory.Functor
