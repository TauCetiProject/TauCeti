/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Promoting nonunital `⋆`-algebra homomorphisms to unital ones

A nonunital `⋆`-algebra homomorphism `f : A →⋆ₙₐ[R] B` between unital `R`-algebras that sends
`1` to `1` automatically commutes with `algebraMap R`, since `algebraMap R A r = r • 1`. This file
packages that promotion as `NonUnitalStarAlgHom.toStarAlgHom`, together with its coercion and
forgetful-unit `simp` lemmas.

## Main declarations

* `NonUnitalStarAlgHom.toStarAlgHom`: promote `f : A →⋆ₙₐ[R] B` with `f 1 = 1` to `A →⋆ₐ[R] B`.
* `NonUnitalStarAlgHom.coe_toStarAlgHom`,
  `NonUnitalStarAlgHom.toNonUnitalStarAlgHom_toStarAlgHom`: `simp` lemmas for function coercion
  and forgetting the unit.
-/

public section

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]

/-- Promote a nonunital `⋆`-algebra homomorphism preserving `1` to a unital `StarAlgHom`. -/
@[expose] def toStarAlgHom (f : A →⋆ₙₐ[R] B) (hf : f 1 = 1) : A →⋆ₐ[R] B where
  toFun := f
  map_one' := hf
  map_mul' := map_mul f
  map_zero' := map_zero f
  map_add' := map_add f
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hf, Algebra.algebraMap_eq_smul_one]
  map_star' := map_star f

/-- Coercing `f.toStarAlgHom hf` to a function recovers `f`. -/
@[simp]
theorem coe_toStarAlgHom (f : A →⋆ₙₐ[R] B) (hf : f 1 = 1) :
    ⇑(f.toStarAlgHom hf) = f :=
  (rfl)

/-- Evaluating `f.toStarAlgHom hf` agrees with `f`. -/
theorem toStarAlgHom_apply (f : A →⋆ₙₐ[R] B) (hf : f 1 = 1) (a : A) :
    f.toStarAlgHom hf a = f a :=
  (rfl)

/-- Forgetting the unit of `f.toStarAlgHom hf` recovers `f`. -/
@[simp]
theorem toNonUnitalStarAlgHom_toStarAlgHom (f : A →⋆ₙₐ[R] B) (hf : f 1 = 1) :
    (f.toStarAlgHom hf).toNonUnitalStarAlgHom = f :=
  (rfl)

end NonUnitalStarAlgHom
