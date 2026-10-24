/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The constructor `End.of` and the algebraic structure of `End X`

Mathlib describes the monoid, additive group and module structures on `CategoryTheory.End X`
through the projection `End.asHom`. This file records the same compatibilities for the
constructor `End.of : (X ⟶ X) → End X`: it sends `𝟙 X` to `1`, a composite `f ≫ g` to the product
`End.of g * End.of f`, and sums, differences, negatives, zero and scalar multiples to the
corresponding operations in `End X`. As `simp` lemmas they push `End.of` inside expressions built
from morphisms `X ⟶ X`, so that algebra maps out of `End X` can then be applied termwise. We also
compute the structure map of an `R`-linear category, `(algebraMap R (End X) r).asHom = r • 𝟙 X`.

An additive linear functor induces an algebra homomorphism on endomorphisms,
`Functor.mapEndAlgHom`, which is injective when the functor is faithful.
-/

public section

namespace CategoryTheory.End

universe w v u

variable {C : Type u} [Category.{v} C] {X : C}

/-- `End.of` sends the identity to `1`. -/
@[simp]
theorem of_id : End.of (𝟙 X) = 1 :=
  rfl

/-- `End.of` sends a composite to the product in the opposite order, since multiplication in
`End X` agrees with function composition. -/
@[simp]
theorem of_comp (f g : X ⟶ X) : End.of (f ≫ g) = End.of g * End.of f :=
  rfl

section Preadditive

variable [Preadditive C]

/-- `End.of` sends the zero morphism to `0`. -/
@[simp]
theorem of_zero : (End.of 0 : End X) = 0 := by
  ext; simp

/-- `End.of` is additive. -/
@[simp]
theorem of_add (f g : X ⟶ X) : End.of (f + g) = End.of f + End.of g := by
  ext; simp

/-- `End.of` commutes with negation. -/
@[simp]
theorem of_neg (f : X ⟶ X) : End.of (-f) = -End.of f := by
  ext; simp

/-- `End.of` commutes with subtraction. -/
@[simp]
theorem of_sub (f g : X ⟶ X) : End.of (f - g) = End.of f - End.of g := by
  ext; simp

/-- `End.of` commutes with scalar multiplication in an `R`-linear category. -/
@[simp]
theorem of_smul {R : Type w} [Semiring R] [Linear R C] (r : R) (f : X ⟶ X) :
    End.of (r • f) = r • End.of f := by
  ext; simp

/-- The structure map `R → End X` of an `R`-linear category sends `r` to `r • 𝟙 X`. -/
@[simp]
theorem algebraMap_asHom {R : Type w} [CommSemiring R] [Linear R C] (r : R) :
    (algebraMap R (End X) r).asHom = r • 𝟙 X := by
  rw [Algebra.algebraMap_eq_smul_one, smul_asHom, one_asHom]

end Preadditive

end CategoryTheory.End

namespace CategoryTheory.Functor

universe w v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [Preadditive C] [Preadditive D] (F : C ⥤ D) (R : Type w) [CommSemiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Additive] [F.Linear R]

/-- An additive linear functor induces an algebra homomorphism on endomorphisms. -/
def mapEndAlgHom (X : C) : End X →ₐ[R] End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := by ext; simp
  map_add' f g := by ext; simp
  commutes' r := by ext; simp

/-- The induced algebra homomorphism acts by the functor on underlying endomorphisms. -/
@[simp]
theorem mapEndAlgHom_asHom (X : C) (f : End X) :
    (F.mapEndAlgHom R X f).asHom = F.map f.asHom :=
  (rfl)

/-- A faithful additive linear functor embeds each endomorphism algebra. -/
theorem mapEndAlgHom_injective [F.Faithful] (X : C) :
    Function.Injective (F.mapEndAlgHom R X) := by
  intro f g h
  apply End.ext
  apply F.map_injective
  simpa only [mapEndAlgHom_asHom] using congrArg End.asHom h

end CategoryTheory.Functor
