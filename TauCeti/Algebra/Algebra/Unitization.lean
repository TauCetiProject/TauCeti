/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization

/-!
# Functoriality and star-lift evaluation of the forced unitization

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

For a nonunital star-algebra homomorphism `φ : A →⋆ₙₐ[R] C` into a unital star `R`-algebra `C`,
Mathlib's `Unitization.starLift φ` lifts `φ` to `Unitization R A →⋆ₐ[R] C`. This file also records
pre-pass `@[simp↓]` evaluation lemmas for `Unitization.starLift` on `inr`, `inl`, and `inl + inr`
(pre-pass is required because Mathlib's `Unitization.starLift_apply` otherwise unfolds `starLift φ`
to an anonymous structure literal before the argument is inspected).

## Main declarations

* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
* `Unitization.starLift_inr`, `Unitization.starLift_inl`, `Unitization.starLift_inl_add_inr`:
  evaluation of `Unitization.starLift` on the canonical inclusions and decomposition.
-/

public section

namespace Unitization

section Map

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

end Map

section StarLift

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [Semiring C] [Algebra R C] [StarRing C] [StarModule R C]

-- Use pre-pass `@[simp↓]` so these fire before Mathlib's `Unitization.starLift_apply` unfolds
-- `starLift φ` into an anonymous `StarAlgHom` structure literal.

/-- The star-algebra lift of a nonunital star-algebra homomorphism restricts to the original
homomorphism on `Unitization.inr`. -/
@[simp↓]
theorem starLift_inr (φ : A →⋆ₙₐ[R] C) (a : A) :
    starLift φ (inr a) = φ a :=
  DFunLike.congr_fun (starLift.symm_apply_apply φ) a

/-- The star-algebra lift of a nonunital star-algebra homomorphism sends `Unitization.inl r` to
`algebraMap R C r`. -/
@[simp↓]
theorem starLift_inl (φ : A →⋆ₙₐ[R] C) (r : R) :
    starLift φ (inl r) = algebraMap R C r := by
  rw [← algebraMap_eq_inl, AlgHomClass.commutes]

/-- Evaluation of `Unitization.starLift φ` on the canonical decomposition `inl r + inr a`. -/
@[simp↓]
theorem starLift_inl_add_inr (φ : A →⋆ₙₐ[R] C) (r : R) (a : A) :
    starLift φ (inl r + inr a) = algebraMap R C r + φ a := by
  rw [map_add, starLift_inl, starLift_inr]

end StarLift

end Unitization
