/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Functoriality of `StarAlgHom.toNonUnitalStarAlgHom`

This file supplements `Mathlib.Algebra.Star.StarAlgHom` with basic functoriality and injectivity
lemmas for forgetting unitality on `StarAlgHom`:

* `StarAlgHom.toNonUnitalStarAlgHom_id`: forgetting unitality sends `StarAlgHom.id` to
  `NonUnitalStarAlgHom.id`.
* `StarAlgHom.toNonUnitalStarAlgHom_comp`: forgetting unitality preserves composition.
* `StarAlgHom.toNonUnitalStarAlgHom_injective`: forgetting unitality is injective.
-/

public section

namespace StarAlgHom

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

/-- Forgetting unitality sends the identity `StarAlgHom` to the identity `NonUnitalStarAlgHom`. -/
@[simp]
theorem toNonUnitalStarAlgHom_id :
    (StarAlgHom.id R A).toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id R A :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality preserves composition of `StarAlgHom`s. -/
@[simp]
theorem toNonUnitalStarAlgHom_comp (f : B →⋆ₐ[R] C) (g : A →⋆ₐ[R] B) :
    (f.comp g).toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom.comp g.toNonUnitalStarAlgHom :=
  NonUnitalStarAlgHom.ext fun _ ↦ rfl

/-- Forgetting unitality on `StarAlgHom` is injective. -/
theorem toNonUnitalStarAlgHom_injective :
    Function.Injective (toNonUnitalStarAlgHom (R := R) (A := A) (B := B)) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

end StarAlgHom
