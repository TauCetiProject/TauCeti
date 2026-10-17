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
-/

public section

namespace Unitization

variable {R A B C : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The unital algebra homomorphism between forced unitizations induced by a homomorphism of
nonunital algebras. -/
noncomputable def map (f : A →ₙₐ[R] B) : Unitization R A →ₐ[R] Unitization R B :=
  lift ((inrNonUnitalAlgHom R B).comp f)

/-- The induced map of unitizations restricts to the original nonunital algebra homomorphism. -/
@[simp]
theorem map_inr (f : A →ₙₐ[R] B) (a : A) : map (R := R) f (inr a) = inr (f a) := by
  simp [map]

/-- The induced map of unitizations is the identity on scalars. -/
@[simp]
theorem map_inl (f : A →ₙₐ[R] B) (r : R) :
    map f (inl r : Unitization R A) = algebraMap R (Unitization R B) r := by
  simp [map]

/-- The scalar component of the induced map of unitizations is unchanged. -/
@[simp]
theorem fst_map (f : A →ₙₐ[R] B) (x : Unitization R A) :
    (map (R := R) f x).fst = x.fst := by
  rw [← inl_fst_add_inr_snd_eq x, map_add]
  simp [algebraMap_eq_inl]

/-- The nonunital-algebra component of the induced map of unitizations is obtained by applying the
original homomorphism. -/
@[simp]
theorem snd_map (f : A →ₙₐ[R] B) (x : Unitization R A) :
    (map (R := R) f x).snd = f x.snd := by
  rw [← inl_fst_add_inr_snd_eq x, map_add]
  simp [algebraMap_eq_inl]

/-- The identity homomorphism induces the identity homomorphism of forced unitizations. -/
@[simp]
theorem map_id : map (R := R) (NonUnitalAlgHom.id R A) = AlgHom.id R (Unitization R A) := by
  apply algHom_ext''
  intro a
  simp

/-- Unitization preserves composition of nonunital algebra homomorphisms. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (R := R) (g.comp f) = (map (R := R) g).comp (map (R := R) f) := by
  apply algHom_ext''
  intro a
  simp

end Unitization
