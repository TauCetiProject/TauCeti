/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization

/-!
# Functoriality of the forced unitization

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

## Main declarations

* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
-/

public section

namespace Unitization

variable {R A B C : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The unital algebra homomorphism between forced unitizations induced by a homomorphism of
nonunital algebras. -/
def map (f : A →ₙₐ[R] B) : Unitization R A →ₐ[R] Unitization R B :=
  lift ((inrNonUnitalAlgHom R B).comp f)

/-- The induced map of unitizations restricts to the original nonunital algebra homomorphism. -/
@[simp]
theorem map_inr (f : A →ₙₐ[R] B) (a : A) : map f (inr a) = inr (f a) := by simp [map]

/-- The induced map of unitizations is the identity on scalars. -/
@[simp]
theorem map_inl (f : A →ₙₐ[R] B) (r : R) :
    map f (inl r : Unitization R A) = algebraMap R (Unitization R B) r := by simp [map]

/-- The scalar component of the induced map of unitizations is unchanged. -/
@[simp]
theorem fst_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).fst = x.fst := by
  simp [map, algebraMap_eq_inl]

/-- The nonunital-algebra component of the induced map of unitizations is obtained by applying the
original homomorphism. -/
@[simp]
theorem snd_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).snd = f x.snd := by
  simp [map, algebraMap_eq_inl]

/-- The induced map of forced unitizations preserves the augmentation `(r, a) ↦ r`. -/
@[simp]
theorem fstHom_comp_map (f : A →ₙₐ[R] B) : (fstHom R B).comp (map f) = fstHom R A :=
  AlgHom.ext fun x ↦ by simp

/-- A surjective homomorphism of nonunital algebras induces a surjective homomorphism of forced
unitizations: `(r, b)` is the image of `(r, a)` for any preimage `a` of `b`. -/
theorem map_surjective {f : A →ₙₐ[R] B} (hf : Function.Surjective f) :
    Function.Surjective (map f) := fun y ↦ by
  obtain ⟨a, ha⟩ := hf y.snd
  exact ⟨inl y.fst + inr a,
    Unitization.ext (by rw [fst_map]; simp) (by rw [snd_map]; simp [ha])⟩

/-- The identity homomorphism induces the identity homomorphism of forced unitizations. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = AlgHom.id R (Unitization R A) :=
  algHom_ext'' fun _ ↦ by simp

/-- Unitization preserves composition of nonunital algebra homomorphisms. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) : map (g.comp f) = (map g).comp (map f) :=
  algHom_ext'' fun _ ↦ by simp

end Unitization
